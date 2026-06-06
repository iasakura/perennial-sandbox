#!/usr/bin/env bash
# Build pipeline for this perennial-cli sandbox.
#
#   Go を書く  →  goose で Rocq に翻訳  →  make で証明チェック
#
# Usage:
#   ./build.sh          # 全部（go build → goose 翻訳 → make）
#   ./build.sh go       # Go のビルド(型チェック)だけ
#   ./build.sh goose    # goose 翻訳だけ（go build もする）
#   ./build.sh make     # 翻訳済み前提で make（証明チェック）だけ
#
# なぜこの手順が要るか（ハマりどころ）:
#  - システム go は 1.25 だが perennial は go 1.26 を要求 → GOTOOLCHAIN=go1.26.0 を前置
#  - go.mod に goose/proofgen が tool 登録されてない → `make` の自動 goose が動かないので
#    perennial 同梱の goose を `--local` で直接呼ぶ（pin と同一バージョンで安全）
#  - 翻訳は済ませたと make に伝えるため .goose-output を touch（さもないと make が
#    動かない goose ステップに突っ込んで死ぬ）
#  - proofgen がたまに不正な src/generatedproof/_ を吐くので毎回掃除
set -euo pipefail

# --- 設定（環境が変わったらここだけ直す） ---
export GOTOOLCHAIN=go1.26.0
PERENNIAL="${PERENNIAL:-/home/ia/ghq/github.com/mit-pdos/perennial}"
GOOSE_SRC="$PERENNIAL/goose"

cd "$(dirname "$0")"

step="${1:-all}"

do_go() {
  echo ">>> go build (型チェック)"
  go build ./...
  echo "    OK"
}

do_goose() {
  echo ">>> goose 翻訳 (Go -> Rocq, perennial 同梱版を --local で使用)"
  go tool perennial-cli goose --local "$GOOSE_SRC"
  rm -rf src/generatedproof/_   # proofgen のゴミ掃除
  echo "    OK -> src/code/... と src/generatedproof/... を更新"
}

do_make() {
  echo ">>> make (.v を .vo にコンパイル = 型検査 + 証明チェック)"
  touch .goose-output          # 翻訳済みと make に伝える
  make
  echo "    OK -> 全 .vo 生成"
}

case "$step" in
  go)    do_go ;;
  goose) do_go; do_goose ;;
  make)  do_make ;;
  all)   do_go; do_goose; do_make ;;
  *) echo "usage: ./build.sh [go|goose|make|all]"; exit 1 ;;
esac

echo "=== done ($step) ==="
