# 開発ワークフロー（手順書）

Go を書く → Rocq に翻訳 → 証明する。3ステップ。

## TL;DR

    ./build.sh        # go build → goose 翻訳 → make（証明チェック）まで一気に

詰まったら段階実行:

    ./build.sh go      # Go の型チェックだけ（実装をいじったらまずこれ）
    ./build.sh goose   # Rocq へ翻訳（go build もする）
    ./build.sh make    # 翻訳済み前提でコンパイル＝証明チェック

## 普段の回し方

1. Go を直す（example/, dll/, codec/ の .go）
2. ./build.sh go で型が通るか確認
3. ./build.sh goose で翻訳。src/code/.../*.v（モデル）と
   src/generatedproof/.../*.v（構造体の補題）が更新される
4. src/proof/*.v に証明を書く／直す
5. ./build.sh make でコンパイル。make=0 なら型検査＋証明チェック通過

注意: Go を変えたら必ず goose からやり直す。make だけだと古い翻訳のままで
「直したのに反映されない」になる。引数なし ./build.sh（=all）が安全。

## 1ファイルだけ手で証明チェック（速い）

make は全部コンパイルし直すので、証明1ファイルだけ試すなら直接:

    set ARGS (sed -E -e '/^#/d' -e "s/'([^']*)'/\1/g" -e 's/-arg //g' _RocqProject)
    rocq compile $ARGS src/proof/dll_proof.v -o src/proof/dll_proof.vo

- 出力名はソースと同じ名前にする（-o .../dll_proof.vo）。違う名前だと
  「Source and target file names must coincide」エラー。
- 覗きたい行に Show. を一時挿入して走らせると、その時点のゴールが出る（デバッグ定番）。

## ディレクトリ

| パス | 中身 | 触る? |
|---|---|---|
| example/ dll/ codec/ | 手書きの Go | ◯ |
| src/proof/*.v | 手書きの証明 | ◯ |
| src/code/.../*.v | goose 翻訳（GooseLang モデル） | × 生成物 |
| src/generatedproof/.../*.v | proofgen（構造体 points-to 補題） | × 生成物 |

生成物（src/code, src/generatedproof）は .gitignore 済み。コミットするのは
Go と src/proof だけ。

## ハマりどころ（build.sh が裏で吸収していること）

- go のバージョン: システム go 1.25 だが perennial は go 1.26 要求。
  GOTOOLCHAIN=go1.26.0 を前置（build.sh が export 済み）。
- goose の在処: go.mod に goose/proofgen が tool 登録されてないので make の自動翻訳は
  動かない。perennial 同梱の goose を --local で直接呼ぶ。これは opam の pin
  （tmp.opam の perennial コミット）と同一版で整合する。go get goose@latest で入る
  v0.10.0 は archive 版で非互換なので使わない。
- .goose-output の touch: 翻訳済みと make に伝えるため。さもないと make が動かない
  goose ステップに入って落ちる。
- src/generatedproof/_ 掃除: proofgen がたまに不正ファイルを吐くので毎回消す。

PERENNIAL の場所が違うマシンでは:

    env PERENNIAL=/path/to/perennial ./build.sh

## 前提（最初の1回だけ）

- opam の perennial switch が active で Perennial 本体が install 済み
  （New / Perennial が user-contrib にある）。これで _RocqProject は -Q src New だけの
  クリーンな状態で VsRocq も make も解決できる。
- ローカルに perennial チェックアウト（goose 同梱）があり tmp.opam の pin と同一コミット。
