import Extras.Syntax

namespace RayMarching

def isqrt (r n b : Nat) : Source.Stmt := s{
  r := 0;
  b := 32768;
  while 0 < b do
    if (r + b) * (r + b) < n + 1 then
      r := r + b;
    end
    b := b >> 1;
  end
}

def len (out : Nat) (x y z : Source.Expr) (tmp b : Nat) : Source.Stmt := s{
  tmp := !(x) * !(x) + !(y) * !(y) + !(z) * !(z);
  !(isqrt out tmp b);
}

def sphere
    (out : Nat) (px py pz cx cy cz rad : Source.Expr)
    (dx dy dz tmp b : Nat) : Source.Stmt := s{
  dx := !(px) - !(cx);
  dy := !(py) - !(cy);
  dz := !(pz) - !(cz);
  !(len out e{dx} e{dy} e{dz} tmp b);
  out := out - !(rad);
}

def torus (out : Nat) (px py pz cx cy cz R r : Source.Expr)
    (dx dy dz tmp b : Nat) : Source.Stmt := s{
  dx := !(px) - !(cx);
  dy := !(py) - !(cy);
  dz := !(pz) - !(cz);
  !(len out e{dx} e{0} e{dz} tmp b);
  dx := out - !(R);
  !(len out e{dx} e{dy} e{0} tmp b);
  out := out - !(r);
}

def unite
    (out mat d2 : Nat) (k : Source.Expr)
    (shape : Source.Stmt) : Source.Stmt := s{
  !(shape);
  if d2 < out then
    out := d2;
    mat := !(k);
  end
}

def scene
    (out mat : Nat) (px py pz : Source.Expr)
    (dx dy dz tmp b d2 : Nat) : Source.Stmt := s{
  out := !(py) + 2560;
  mat := 1;
  !(unite out mat d2 e{3}
      (sphere d2 px py pz e{0} e{0 - 1536} e{6144} e{1024} dx dy dz tmp b));
  !(unite out mat d2 e{4}
      (torus d2 px py pz e{0 - 2662} e{0 - 2304} e{7680} e{1024} e{256} dx dy dz tmp b));
  !(unite out mat d2 e{8}
      (torus d2 px py pz e{1946} e{0 - 2406} e{5222} e{614} e{154} dx dy dz tmp b));
  !(unite out mat d2 e{5}
      (sphere d2 px py pz e{2867} e{0 - 1843} e{8704} e{717} dx dy dz tmp b));
  !(unite out mat d2 e{6}
      (sphere d2 px py pz e{0 - 1331} e{0 - 2150} e{4403} e{410} dx dy dz tmp b));
  !(unite out mat d2 e{7}
      (sphere d2 px py pz e{717} e{0 - 2253} e{4096} e{307} dx dy dz tmp b));
}

def march
    (out mat t : Nat) (ox oy oz rx ry rz : Source.Expr)
    (i px py pz dx dy dz tmp b d2 : Nat) : Source.Stmt := s{
  t := 0; i := 0; out := 1024;
  while (i < 128) * (8 < out) * (t < 20480) do
    px := !(ox) + (t * !(rx) >> 10);
    py := !(oy) + (t * !(ry) >> 10);
    pz := !(oz) + (t * !(rz) >> 10);
    !(scene out mat e{px} e{py} e{pz} dx dy dz tmp b d2);
    t := t + out;
    i := i + 1;
  end
}

-- 出力
def out : Nat := 0
-- レイの方向ベクトル
def rx : Nat := 1
def ry : Nat := 2
def rz : Nat := 3
-- 進行方向へのパラメータ
def t : Nat := 4
-- ループカウンタ
def i : Nat := 5
-- レイ先端の座標
def px : Nat := 6
def py : Nat := 7
def pz : Nat := 8
-- 計算用の一時変数
def dx : Nat := 9
def dy : Nat := 10
def dz : Nat := 11
def tmp : Nat := 12
def b : Nat := 13
-- 法線
def nx : Nat := 14
def ny : Nat := 15
def nz : Nat := 16
def d1 : Nat := 17
def mat : Nat := 18
def d2 : Nat := 19
def br : Nat := 20
def ox : Nat := 21
def oy : Nat := 22
def oz : Nat := 23
def m2 : Nat := 24
def prog : Source.Stmt := s{
  !(march br mat
      t e{0} e{0} e{0} e{rx} e{ry} e{rz}
      i px py pz dx dy dz tmp b d2);
  if br < 9 then
    !(scene nx mat e{px + 64} e{py} e{pz} dx dy dz tmp b d2);
    !(scene d1 mat e{px - 64} e{py} e{pz} dx dy dz tmp b d2);
    nx := (nx - d1) * 8;
    !(scene ny mat e{px} e{py + 64} e{pz} dx dy dz tmp b d2);
    !(scene d1 mat e{px} e{py - 64} e{pz} dx dy dz tmp b d2);
    ny := (ny - d1) * 8;
    !(scene nz mat e{px} e{py} e{pz + 64} dx dy dz tmp b d2);
    !(scene d1 mat e{px} e{py} e{pz - 64} dx dy dz tmp b d2);
    nz := (nz - d1) * 8;
    br := (nx * (0 - 512) + ny * 724 + nz * (0 - 512)) >> 10;
    if br < 0 then
      br := 0;
    end
    if 1023 < br then
      br := 1023;
    end
    tmp := (px >> 10) + (pz >> 10);
    tmp := tmp - (tmp >> 1) * 2;
    if (mat < 3) * tmp then
      mat := 2;
    end
    ox := px + (nx >> 4);
    oy := py + (ny >> 4);
    oz := pz + (nz >> 4);
    !(march out m2
        t e{ox} e{oy} e{oz} e{0 - 512} e{724} e{0 - 512}
        i px py pz dx dy dz tmp b d2);
    if out < 9 then
      br := br >> 2;
    end
    br := (br * 3 >> 2) + 256;
    out := (mat * 256) + (br >> 2);
  else
    out := 0;
  end
}

end RayMarching
