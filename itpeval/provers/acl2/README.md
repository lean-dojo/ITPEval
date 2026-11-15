# ACL2 adapter

This directory contains the ACL2 adapter for `ITPEval`.

Files:
- `install.sh`: installs ACL2 locally under `ITPEVAL_PREFIX/acl2`
- `check.sh`: runs a tiny batch proof check
- `hello/hello.lsp`: the smoke-test script

Install strategy:
- prefer a local `.deb` extraction of the Debian ACL2 package on Linux
- wire an existing `ACL2_HOME` / `ITPEVAL_ACL2_HOME` if provided
- fall back to downloading the Debian package into the local prefix

Useful overrides:
- `ACL2_DEB_URL`
- `ACL2_VERSION`
- `ITPEVAL_ACL2_HOME`
- `ITPEVAL_ACL2_DEB`
