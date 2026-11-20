"""Serve built documentation with an optional local Python kernel. Run from the repository root."""
import os
from pathlib import Path
import re
from urllib.parse import parse_qsl, urlencode

from jupyter_server.auth.decorator import allow_unauthenticated
from jupyter_server.base.handlers import JupyterHandler
from jupyter_server.serverapp import ServerApp
from tornado.web import StaticFileHandler

SITE = Path(__file__).resolve().parent / "dist"


class Documentation(JupyterHandler, StaticFileHandler):
    """Serve only the documentation tree. Kernel requests use Jupyter's own authentication."""

    def compute_etag(self):
        # The same URL can point to a new build while this server is running.
        return None

    def set_extra_headers(self, path):
        self.set_header("Cache-Control", "no-store")

    def should_return_304(self):
        # Older previews may still send validators for the previous build.
        return False

    @allow_unauthenticated
    async def get(self, path, **kwargs):
        if "token" in self.request.query_arguments:
            args = [(k, v) for k, v in parse_qsl(self.request.query) if k != "token"]
            self.redirect(self.request.path + ("?" + urlencode(args) if args else ""))
            return
        self.set_header("Referrer-Policy", "no-referrer")
        self.set_cookie("itpeval_examples", "local", samesite="Strict")
        # Jupyter expects this browser's XSRF token on state-changing requests.
        _ = self.xsrf_token
        await StaticFileHandler.get(self, path, **kwargs)

    @allow_unauthenticated
    async def head(self, path, **kwargs):
        await self.get(path, include_body=False, **kwargs)


def routes():
    # Let Jupyter own /api, /login and its other routes. Serve only build products here.
    entries = "|".join(re.escape(p.name) for p in sorted(SITE.glob("*")) if p.name != "index.html")
    options = {"path": str(SITE), "default_filename": "index.html"}
    return [(r"/()", Documentation, options), (rf"/((?:{entries})(?:/.*)?)", Documentation, options)]


default_handlers = routes()


if __name__ == "__main__":
    if not (SITE / "index.html").is_file():
        raise SystemExit("Build the documentation first with python -m mkdocs build.")
    # Shell examples and their child interpreters should import this checkout too.
    paths = [str(SITE.parents[1]), *filter(None, os.getenv("PYTHONPATH", "").split(os.pathsep))]
    os.environ["PYTHONPATH"] = os.pathsep.join(dict.fromkeys(paths))
    ServerApp.launch_instance(argv=[
        f"--ServerApp.root_dir={SITE.parents[1]}",
        "--ServerApp.ip=127.0.0.1", "--ServerApp.port=8764", "--ServerApp.port_retries=0",
        "--ServerApp.use_redirect_file=False", "--ServerApp.default_url=/", "--ServerApp.extra_services=website.preview",
        "--MappingKernelManager.cull_idle_timeout=600",
        "--MappingKernelManager.cull_interval=60", "--ServerApp.open_browser=True",
    ])
