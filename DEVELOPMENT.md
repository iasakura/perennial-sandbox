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
Go を書く  →  perennial-cli goose で .v に翻訳(goose+proofgen)
          →  Iris/Perennial で正しさを証明  →  make でコンパイル & 証明チェック
```

## 普通のフロー（これが標準）

```fish
# --- セットアップ(初回のみ) ---
# (1) goose/proofgen を go tool として登録(init が本来やる分)
go get -tool github.com/goose-lang/goose/cmd/goose@latest \
             github.com/goose-lang/goose/cmd/proofgen@latest
# (2) Perennial 本体を opam に入れる(make が New.* / Perennial.* を解決するため)
opam install perennial          # tmp.opam の pin コミットが user-contrib に入る

# --- 毎回 ---
# Go を書く(go_path = "." 配下のパッケージ)
go tool perennial-cli goose     # CLI が goose と proofgen を実行
                                #   → src/code/...(翻訳モデル), src/generatedproof/...(証明スケルトン)
make                            # rocq dep → .v を .vo にコンパイル(=型検査+証明チェック)
```

`make` が `EXIT=0` なら、生成コードの型検査と、proofgen が出した Iris 証明
（`Qed.`）まで全て通った＝**検証成功**。`perennial-cli` と `Makefile` を使う意味は
まさにここ: ツール版が go.mod で固定され、誰がチェックアウトしても同じ手順で回る。

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

## このマシンで標準フローが詰まった2つの落とし穴

上の「普通のフロー」をこの環境でそのまま実行すると2箇所で止まった。原因と回避を
記録する（どちらも本質は **セットアップ未完**であって、フローは壊れていない）。

### 落とし穴1: goose のバージョンが pin と合わない

`go get -tool goose@latest` が引くのは、archive 済み `goose-lang/goose` の
**凍結版 v0.10.0**。一方 `tmp.opam` が pin する Perennial は `f884a505`。両者は
非互換で、v0.10.0 が生成した `.v` は新しい `New.golang` 理論とずれて
`Cannot infer ... GoGlobalContext`（type class instance not found）でコンパイル不能。
さらに v0.10.0 のバイナリは go1.26 と非互換で `unknown GOEXPERIMENT synchashtriemap`
で panic する。

**回避**: goose 開発は Perennial 本体に移動済み（archive 通知）。ローカルに
`~/ghq/github.com/mit-pdos/perennial`（HEAD `f884a505` = pin と一致）があるので、
CLI の `--local` でその同梱 goose を使い、pin と同一バージョンで翻訳する:

```fish
set P ~/ghq/github.com/mit-pdos/perennial
GOTOOLCHAIN=go1.26.0 go tool perennial-cli goose --local $P/goose
```

> `--local` は `$P/goose/cmd/{goose,proofgen}` をその場でビルドして実行する。
> このビルドには go1.26 が要る（システムは 1.25.10、`$P/go.work` が go 1.26 要求）。
> `GOTOOLCHAIN=go1.26.0` を前置すれば go が 1.26 を自動DLして使う。
> 翻訳された `.v` 自体のコンパイル（make 側）は 1.25.10 のままで問題ない。

### 落とし穴2: Perennial が opam install されていない

`make` は `New.proof.proof_prelude` など `New.*` / `Perennial.*` を require するが、
このマシンの Perennial は in-tree ビルドのみで **opam 未インストール**（user-contrib に
無い）。そのため `rocq dep` が
`library New.proof.proof_prelude ... not found in the loadpath` で落ちる。

**本来の回避**: `opam install perennial`（pin コミットを user-contrib に入れる）。
これで `make` が無改変で一発で通る。

**今回の暫定回避**: `_RocqProject` に in-tree perennial を一時的に足して `make` を
完走させた（push 前に戻す）:

```
-Q /abs/path/to/perennial/new New
-Q /abs/path/to/perennial/src Perennial
```

> 注意: in-tree を `-Q` で直接指すと、`make` が Perennial 側の `.v` まで「ビルド対象」と
> みなして再コンパイルし、既存 `.vo` と矛盾（`inconsistent assumptions`）を起こすこと
> がある。特に `_RocqProject` を編集するとその mtime が全 `.vo` の依存に効き、Perennial
> の `.vo` を巻き込んで再ビルドしてしまう。`opam install` ならライブラリ扱いになり、この
> 問題は起きない。暫定回避を使うなら `_RocqProject` の mtime を Perennial の `.vo` より
> 古くしておく（`touch -d <古い日付> _RocqProject`）。

## サンドボックスについて

go のビルド/実行や rocq compile（go ツールチェーン経由）は `~/.cache/go-build` と
`~/go/pkg/mod` への書き込みが要る。サンドボックス下では read-only で失敗するので、
これらはサンドボックス無効で実行する。ファイル読み書き（`src/` や `$TMPDIR`）だけの
操作はサンドボックスのままでよい。

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

## 証明チェック（検証済み）

上記の落とし穴を回避した状態で `make` を実行すると、`src/` 配下の `.v` が `.vo` に
コンパイルされる。型検査に加え、proofgen が出した Iris 証明（`Qed.`）まで検査される
ので、これが「証明チェック」になる。実際にこの環境で完走した:

```
$ make                                  # MAKE_EXIT=0
ROCQ compile src/code/.../example.v
ROCQ compile src/generatedproof/.../example.v
$ find src -name '*.vo'
src/code/github_com/iasakura/perennial_sandbox/example.vo
src/generatedproof/github_com/iasakura/perennial_sandbox/example.vo
```

proofgen が生成した `Counter` の Iris points-to 述語やフィールドアクセス補題
（`solve_typed_pointsto_agree` / `solve_into_val_typed_struct` /
`solve_pointsto_access_struct`）が `Qed.` で閉じている＝**検証成功**。

### ロードパスの考え方（なぜ make が New.* を解決できるか）

生成コードは `New.golang.*` / `New.proof.*` / `New.code.*` を require する。`make` が
これらを見つけられるのは、Perennial の `new/`（論理名 `New`）と `src/`（論理名
`Perennial`）がロードパスにあるから。本来は `opam install perennial` で user-contrib に
入る。今回の暫定回避では `_RocqProject` に下記を足して同じ `New` 名前空間に重ねた:

- `-Q src New`              … 自分の `src/code/...` → `New.code.*`、`src/generatedproof/...` → `New.generatedproof.*`
- `-Q <perennial>/new New`   … `New.golang.*`, `New.proof.*`, `New.theory.*` など
- `-Q <perennial>/src Perennial` … `Perennial.*`（間接依存）
