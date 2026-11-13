#!/usr/bin/env bash
# Build and locally serve the whole site as GitHub Pages lays it out (docgen-action in
# .github/workflows/blueprint.yml):
#   /               Jekyll home page (home_page/)
#   /blueprint/     leanblueprint web output (blueprint/web/)
#   /blueprint.pdf  leanblueprint pdf output (blueprint/print/print.pdf)
#   /docs/          doc-gen4 output (.lake/build/doc/)
# Links from the blueprint to the docs are rewritten from the \dochome URL to the local /docs.
#
# Jekyll runs inside the Nix dev shell of home_page/flake.nix (Ruby 3.4, as in CI) when `nix` is
# available, otherwise with the system `bundle`. Gems are installed into home_page/vendor/bundle.
set -euo pipefail

usage() {
  cat <<EOF
Usage: blueprint/serve.sh [options]

  -p, --port PORT   port to serve on (default 8000)
      --no-docs     skip \`lake build\` and lints (reuse .lake/build/doc)
      --no-blueprint skip leanblueprint all builds (reuse existing output)
      --no-jekyll   skip the Jekyll build (reuse home_page/_site)
      --no-build    skip all builds; only assemble the site and serve it
      --no-serve    build and assemble, but do not start the server
  -h, --help        show this help

The first docs build documents all of Mathlib and can take hours; later builds are incremental.
EOF
}

port=8000
build_docs=1
build_blueprint=1
build_jekyll=1
serve=1
while [[ $# -gt 0 ]]; do
  case "$1" in
    -p|--port) port="$2"; shift 2 ;;
    --no-docs) build_docs=0; shift ;;
    --no-blueprint) build_blueprint=0; shift ;;
    --no-jekyll) build_jekyll=0; shift ;;
    --no-build) build_docs=0; build_blueprint=0; build_jekyll=0; shift ;;
    --no-serve) serve=0; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
site="$root/home_page/_site"
step() { printf '\n==> %s\n' "$*"; }

if (( build_docs )); then
  step "Building API docs (lake build DetPoly:docs LEAN_Warmup:docs)"
  lake exe mk_all
  lake build
  lake lint
  lake build DetPoly:docs LEAN_Warmup:docs
fi

if (( build_blueprint )); then
  step "Building blueprint (all)"
  uv run leanblueprint all
  uv run leanblueprint checkdecls
fi

if (( build_jekyll )); then
  step "Building home page (Jekyll)"
  # Point {{ site.url }} at the local server instead of GitHub Pages.
  override="$(mktemp --suffix=.yml)"
  trap 'rm -f "$override"' EXIT
  printf 'url: "http://localhost:%s"\n' "$port" > "$override"
  rm -f "$site/docs"  # our symlink from a previous run; keep Jekyll's cleaner away from it
  jekyll_cmd="bundle check >/dev/null 2>&1 || bundle install
  bundle exec jekyll build --config _config.yml,'$override'"
  if command -v nix >/dev/null; then
    (cd home_page && nix --extra-experimental-features 'nix-command flakes' \
      develop . --command bash -euc "$jekyll_cmd")
  else
    (cd home_page && BUNDLE_PATH=vendor/bundle bash -euc "$jekyll_cmd")
  fi
fi

step "Assembling site in home_page/_site"
[[ -d blueprint/web ]] || { echo "blueprint/web missing; run without --no-build" >&2; exit 1; }
mkdir -p "$site"
rm -f "$site/docs"
rm -rf "$site/blueprint" "$site/blueprint.pdf"
cp -r blueprint/web "$site/blueprint"
dochome="$(sed -n 's/^\\dochome{\(.*\)}.*/\1/p' blueprint/src/web.tex)"
if [[ -n "$dochome" ]]; then
  find "$site/blueprint" -name '*.html' -exec sed -i "s#${dochome%/}/#/docs/#g" {} +
fi
if [[ -f blueprint/print/print.pdf ]]; then
  cp blueprint/print/print.pdf "$site/blueprint.pdf"
else
  echo "warning: blueprint/print/print.pdf missing; /blueprint.pdf will 404" >&2
fi
if [[ -d .lake/build/doc ]]; then
  ln -s "$root/.lake/build/doc" "$site/docs"  # 1+ GB, so link rather than copy
else
  echo "warning: .lake/build/doc missing; /docs/ will 404" >&2
fi

if (( serve )); then
  step "Serving on http://localhost:$port/ (Ctrl-C to stop)"
  exec python3 -m http.server "$port" --bind 127.0.0.1 --directory "$site"
fi
