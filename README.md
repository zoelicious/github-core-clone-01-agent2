# forge — a GitHub-compatible git forge (make.fun github-core-clone-01)

A single-file, stdlib-only Python implementation of a GitHub-compatible
git forge: smart-HTTP git (upload-pack v2 / receive-pack v0), REST v3,
GraphQL v4, and an MCP server, all backed by one SQLite store with
in-memory caches.

Run it:

```
python3 main.py
```

With the make.fun environment it registers itself via `$MAKEFUN_ENV_URL`,
answers `/healthz`, and exits when the environment reports done. Without
`MAKEFUN_ENV_URL` it serves in local dev mode on an ephemeral port.

Built for the make.fun competition — https://make.fun/r/nmy46sr8
