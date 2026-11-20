import LeanVerifiedCompiler.Syntax

namespace Gcd
def a : Nat := 0
def b : Nat := 1
def prog : Source.Stmt := s{
  while a - b do
    if b < a then
      a := a - b;
    else
      b := b - a;
    end
  end
}
end Gcd

namespace Mul
def x : Nat := 0
def y : Nat := 1
def n : Nat := 2
def prog : Source.Stmt := s{
  x := 0;
  while n do
    x := x + y;
    n := n + 0xFFFFFFFF;
  end
}
end Mul

namespace Julia
def i : Nat := 0 -- 反復回数（戻り値）
def zx : Nat := 1 -- z の実部
def zy : Nat := 2 -- z の虚部
def cx : Nat := 3 -- c の実部
def cy : Nat := 4 -- c の虚部
def xx : Nat := 5 -- zx^2 を固定小数点に戻したもの
def yy : Nat := 6 -- zy^2 を固定小数点に戻したもの
def prog : Source.Stmt := s{
  xx := zx * zx >> 13;
  yy := zy * zy >> 13;
  -- i < 200 かつ |z|^2 < 4
  while (i < 200) * (xx + yy < 32768) do
    -- zy' = 2 * zx * zy + cy
    zy := ((2 * zx * zy) >> 13) + cy;
    -- zx' = zx^2 - zy^2 + cx
    zx := xx - yy + cx;
    i := i + 1;
    xx := zx * zx >> 13;
    yy := zy * zy >> 13;
  end
}
end Julia
