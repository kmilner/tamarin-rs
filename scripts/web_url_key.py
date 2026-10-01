"""Stable manifest-key normalization shared by crawl and comparison code."""

import re


_TRACE_IDX_RE = re.compile(r"/thy/trace/\d+/")
_EQUIV_IDX_RE = re.compile(r"/thy/equiv/\d+/")


def norm_indices(value: str) -> str:
    value = _TRACE_IDX_RE.sub("/thy/trace/#/", value)
    return _EQUIV_IDX_RE.sub("/thy/equiv/#/", value)


def norm_url_key(url: str) -> str:
    """Normalize a URL for use as an index-agnostic manifest key."""
    return norm_indices(url)
