# 『コンパイラ証明技法』サポートサイト

技術書典 21 で頒布した同人誌『コンパイラ証明技法 - Lean による Wasm コンパイラ実装』のサンプルコードです。

## ビルド方法

```sh
git clone https://github.com/y-taka-23/lean-verified-compiler.git
cd lean-verified-compiler

lake build
lake exe lean-verified-compiler
wat2wasm out/julia.wat -o out/julia.wasm

python3 -m http.server
# http://localhost:8000/web/ をブラウザで開く
```

### 正誤表

N/A
