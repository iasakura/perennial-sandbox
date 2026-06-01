# 開発メモ: このプロジェクトの遊び方

`perennial-cli init` で生成された Perennial 検証プロジェクト（Go module:
`github.com/iasakura/perennial-sandbox`）の触り方をまとめる。

## 全体像

これは「Go で書いたプログラムを Rocq(旧 Coq)上のモデルに変換し、Iris/Perennial
で正しさを形式証明する」ためのプロジェクト骨格。中心となるツールが2つある。

- **perennial-cli** … Perennial 検証プロジェクトを管理する CLI
  （<https://github.com/mit-pdos/perennial-cli>）。`init` / `goose` / `opam` /
  `install` などのサブコマンドを持つ。`go tool perennial-cli` で起動する。
- **goose** … Go を Rocq のモデル（GooseLang）に翻訳するトランスレータ。
  **翻訳方向は Go → Rocq**（逆ではない）。

ワークフロー:

```
Go を書く  →  goose で .v に翻訳  →  proofgen で証明スケルトン生成
          →  Iris/Perennial で正しさを証明  →  make でコンパイル & 証明チェック
```

## ディレクトリ / ファイル構成

| パス | 役割 |
|---|---|
| `goose.toml`      | goose の設定。`rocq="src"`（出力先ルート）, `go_path="."`（Go ソース） |
| `<name>.opam`（`tmp.opam`） | 依存（特に perennial の git pin コミット）を管理 |
| `_RocqProject`    | Rocq のロードパスとコンパイル引数。現状 `-Q src New` のみ |
| `Makefile`        | goose 実行 → `rocq dep` → `.v` を `.vo` にコンパイル |
| `src/`            | Rocq ソース。`src/code/...`（goose 生成）, `src/generatedproof/`（proofgen 生成）が入る |
| `example/example.go` | 翻訳デモ用に手書きした最小の Go パッケージ |

> `src/code/**/*.v` と `src/generatedproof/` は **生成物**で `.gitignore` 済み。

## 環境の前提（このマシン固有のハマりどころ）

1. **goose の入手先**: 旧 `goose-lang/goose` は 2026-04 に archive され
   （凍結版 v0.10.0）、開発は Perennial 本体に移動した。ローカルに
   `~/ghq/github.com/mit-pdos/perennial`（HEAD `f884a505` = `tmp.opam` の pin と
   一致）があり、その中の `goose/cmd/goose` と `goose/cmd/proofgen` を使う。
2. **Go ツールチェーン**: システムの go は 1.25.10 だが、perennial の `go.work` は
   `go 1.26` を要求する。`GOTOOLCHAIN=go1.26.0` を前置すると go が 1.26 を自動DL
   して使う（DL 済み: `~/go/pkg/mod/golang.org/toolchain@v0.0.1-go1.26.0...`）。
3. **サンドボックス**: go のビルド/実行は `~/.cache/go-build` と `~/go/pkg/mod` への
   書き込みが要る。サンドボックス下では read-only になり失敗するので、これらは
   サンドボックス無効で実行する。

## 手順（検証済み）

### 1. goose / proofgen をビルド

```fish
set P ~/ghq/github.com/mit-pdos/perennial
cd $P; and GOTOOLCHAIN=go1.26.0 go build -o $TMPDIR/goose    ./goose/cmd/goose
cd $P; and GOTOOLCHAIN=go1.26.0 go build -o $TMPDIR/proofgen ./goose/cmd/proofgen
```

### 2. Go → Rocq 翻訳

```fish
cd ~/tmp/tmp
$TMPDIR/goose    -out src/code           -dir . ./...
$TMPDIR/proofgen -out src/generatedproof -dir . ./...   # .v.toml がある場合は -configdir src/code を付ける
```

`example/example.go` から `src/code/github_com/iasakura/perennial_sandbox/example.v`
が生成される（1 パッケージ → 1 ファイル、先頭は `From New.golang Require Import defn.`）。

> 備考: 本来は `go tool perennial-cli goose` 一発で上記2つを呼ぶ設計だが、
> このプロジェクトの go.mod には goose/proofgen が tool 登録されておらず
> （`init` 時の `go get` が未完了）、かつ v0.4.4 経由だと go1.26 の壁に当たるため、
> ここでは goose を直接叩いている。

## 翻訳結果の読み方

`example/example.go` と生成された `example.v` の対応:

| Go | Rocq (GooseLang) |
|---|---|
| `const MaxRetries uint64 = 3` | `Definition MaxRetries ... := #(W64 3)` （64bit 語） |
| `func Add(a, b uint64) uint64 { return a+b }` | `Addⁱᵐᵖˡ := λ: "a" "b", ... return: (![..]"a" +⟨go.uint64⟩ ![..]"b")` |
| `for i < n { ... }` | `(for: (λ:<>, ![..]"i" <⟨go.uint64⟩ ![..]"n"); ...)` |
| `type Counter struct { n uint64 }` | `Module Counter ... Record t := mk { n' : w64 }` + `Counter'fds` |
| `func (c *Counter) Inc()` | `Counter__Incⁱᵐᵖˡ := λ: "c" <>, ...` + `MethodUnfold (PointerType Counter) "Inc"` |

ポイント:

- 各変数は `GoAlloc` でヒープ確保され、`![go.uint64]` で読み、`<-[go.uint64]` で
  書く。Go の代入セマンティクスを忠実にモデル化している。
- 元コードの行番号（`go: example.go:9:6`）とコメントが保持される。
- 末尾の `Assumptions` クラス（`Add_unfold`, `SumTo_unfold` …）が、**証明を書くときの
  接続点**になる。

## まだやっていないこと / 次の選択肢

- **proofgen のスケルトン**: `src/generatedproof` の生成は未実施（証明の出発点）。
- **`make` でのコンパイル**: 生成された `.v` は `From New.golang Require Import defn`
  に依存するため、`_RocqProject` の `-Q src New` だけでは足りない。Perennial の `New`
  をロードパスに載せる必要がある。いずれか:
  - `opam install perennial`（pin コミットを user-contrib にインストール）、または
  - `_RocqProject` に `-Q ~/ghq/github.com/mit-pdos/perennial/new New`（＋依存）を追加。
  現状 Perennial は in-tree ビルドのみで opam 未インストール。
