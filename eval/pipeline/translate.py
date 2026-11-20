from __future__ import annotations

import os


def _load_keys() -> None:
    """Load .env if python-dotenv is available, otherwise rely on environment."""
    try:
        from dotenv import load_dotenv
        from pathlib import Path
        load_dotenv(Path(__file__).parent.parent / ".env")
    except ImportError:
        pass


_loaded = False


def _ensure_loaded() -> None:
    global _loaded
    if not _loaded:
        # Load local API keys lazily so import-only commands do not require credentials
        _load_keys()
        _loaded = True


def translate(
    *,
    system_prompt: str,
    user_prompt: str,
    model_cfg: dict,
    max_tokens: int = 16000,
    temperature: float = 0.0,
) -> str:
    """Call the appropriate LLM API and return the generated proof string."""
    _ensure_loaded()

    provider = model_cfg["provider"]
    model_id = model_cfg["id"]

    # Provider branches normalize each SDK response to a single text string
    if provider == "anthropic":
        import anthropic

        client = anthropic.Anthropic(api_key=os.environ["ANTHROPIC_API_KEY"])
        message = client.messages.create(
            model=model_id,
            max_tokens=max_tokens,
            temperature=temperature,
            system=system_prompt,
            messages=[{"role": "user", "content": user_prompt}],
        )
        text = message.content[0].text
        if not text:
            raise ValueError(f"Empty response (stop_reason={message.stop_reason})")
        return text

    elif provider == "openai":
        import openai

        client = openai.OpenAI(api_key=os.environ["OPENAI_API_KEY"])
        response = client.chat.completions.create(
            model=model_id,
            max_completion_tokens=max_tokens,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ],
        )
        text = response.choices[0].message.content
        if not text:
            raise ValueError(f"Empty response (finish_reason={response.choices[0].finish_reason})")
        return text

    elif provider == "groq":
        import openai

        client = openai.OpenAI(
            api_key=os.environ["GROQ_API_KEY"],
            base_url="https://api.groq.com/openai/v1",
        )
        response = client.chat.completions.create(
            model=model_id,
            max_tokens=max_tokens,
            temperature=temperature,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ],
        )
        text = response.choices[0].message.content
        if not text:
            raise ValueError(f"Empty response (finish_reason={response.choices[0].finish_reason})")
        return text

    elif provider == "openrouter":
        import openai

        client = openai.OpenAI(
            api_key=os.environ["OPENROUTER_API_KEY"],
            base_url="https://openrouter.ai/api/v1",
            timeout=600.0,
        )
        response = client.chat.completions.create(
            model=model_id,
            max_tokens=max_tokens,
            temperature=temperature,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ],
        )
        if not response.choices:
            raise ValueError("No choices in response (model may have returned an error)")
        text = response.choices[0].message.content
        if not text:
            raise ValueError(f"Empty response (finish_reason={response.choices[0].finish_reason})")
        return text

    elif provider == "gemini":
        from google import genai
        from google.genai import types as genai_types

        client = genai.Client(api_key=os.environ["GEMINI_API_KEY"])
        response = client.models.generate_content(
            model=model_id,
            contents=user_prompt,
            config=genai_types.GenerateContentConfig(
                system_instruction=system_prompt,
                max_output_tokens=max_tokens,
                temperature=temperature,
            ),
        )
        text = response.text
        if not text:
            raise ValueError("Empty response from Gemini")
        return text

    else:
        raise ValueError(f"Unknown provider: {provider}")
