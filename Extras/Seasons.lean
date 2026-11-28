import Extras.Syntax

namespace Seasons

-- 座標と高さは 1/256 単位の固定小数点

def lit (v : Int) : Source.Expr := .lit (BitVec.ofInt 32 v)

def out : Nat := 0
def mode : Nat := 1
def a0 : Nat := 2
def a1 : Nat := 3
def a2 : Nat := 4
def a3 : Nat := 5
def a4 : Nat := 6
def a5 : Nat := 7
def a6 : Nat := 8
def a7 : Nat := 9
def a8 : Nat := 10
def a9 : Nat := 11
def a10 : Nat := 12
def a11 : Nat := 13
def a12 : Nat := 14
def a13 : Nat := 15
def nxi : Nat := 16
def nyi : Nat := 17
def nfx : Nat := 18
def nfy : Nat := 19
def nsx : Nat := 20
def nsy : Nat := 21
def nha : Nat := 22
def nhb : Nat := 23
def nhc : Nat := 24
def nhd : Nat := 25
def nab : Nat := 26
def ncd : Nat := 27
def nht : Nat := 28
def nv : Nat := 29
def tX : Nat := 30
def tZ : Nat := 31
def tn : Nat := 32
def dq : Nat := 33
def dr : Nat := 34
def di : Nat := 35
def dtop : Nat := 36
def da : Nat := 37
def sr : Nat := 38
def sb : Nat := 39
def si : Nat := 40
def sj : Nat := 41
def sw : Nat := 42
def sp : Nat := 43
def sf : Nat := 44
def b1 : Nat := 45
def b2 : Nat := 46
def cr : Nat := 47
def cg : Nat := 48
def cb : Nat := 49
def hr : Nat := 50
def hg : Nat := 51
def hb : Nat := 52
def m0 : Nat := 53
def m1 : Nat := 54
def m2 : Nat := 55
def m3 : Nat := 56
def m4 : Nat := 57
def m5 : Nat := 58
def m6 : Nat := 59
def m7 : Nat := 60
def m8 : Nat := 61
def m9 : Nat := 62
def m10 : Nat := 63
def m11 : Nat := 64
def m12 : Nat := 65
def m13 : Nat := 66
def m14 : Nat := 67
def m15 : Nat := 68

-- 0..1023
def hash32 (o : Nat) (x y : Source.Expr) (t : Nat) : Source.Stmt := s{
  t := !(x) * 374761393 + !(y) * 668265263;
  t := (t - (t >> 13)) * 1274126177;
  t := t + (t >> 16);
  o := (t >> 8) - (t >> 18) * 1024;
}

-- バリューノイズ（格子の間隔 2^sc）。0..1023
def noise (o : Nat) (x y : Source.Expr) (sc : Nat) : Source.Stmt :=
  let one := lit (2 ^ sc)
  let sh := lit sc
  let sh2 := lit (2 * sc)
  s{
  nxi := !(x) >> !(sh);
  nyi := !(y) >> !(sh);
  nfx := !(x) - nxi * !(one);
  nfy := !(y) - nyi * !(one);
  nsx := nfx * nfx * (3 * !(one) - 2 * nfx) >> !(sh2);
  nsy := nfy * nfy * (3 * !(one) - 2 * nfy) >> !(sh2);
  !(hash32 nha e{nxi} e{nyi} nht);
  !(hash32 nhb e{nxi + 1} e{nyi} nht);
  !(hash32 nhc e{nxi} e{nyi + 1} nht);
  !(hash32 nhd e{nxi + 1} e{nyi + 1} nht);
  nab := nha + ((nhb - nha) * nsx >> !(sh));
  ncd := nhc + ((nhd - nhc) * nsx >> !(sh));
  o := nab + ((ncd - nab) * nsy >> !(sh));
}

def terrain (o : Nat) (x z : Source.Expr) : Source.Stmt := s{
  tX := !(x) >> 4;
  tZ := !(z) >> 4;
  !(noise nv e{tX} e{tZ} 8);
  tn := nv * 2;
  !(noise nv e{tX} e{tZ} 6);
  tn := tn + nv;
  !(noise nv e{tX} e{tZ} 5);
  tn := tn + (nv >> 1);
  o := (tn - 1350) * 328 >> 8;
}

-- q := a / b（0 <= a < 2^nb、0 < b）
def divide (q : Nat) (a b : Source.Expr) (nb : Nat) : Source.Stmt := s{
  da := !(a) * !(lit (2 ^ (31 - nb)));
  dq := 0;
  dr := 0;
  di := !(lit nb);
  while 0 < di do
    dtop := da >> 30;
    dr := dr * 2 + dtop;
    da := (da - dtop * 1073741824) * 2;
    dq := dq * 2;
    if !(b) - 1 < dr then
      dr := dr - !(b);
      dq := dq + 1;
    end
    di := di - 1;
  end
  q := dq;
}

-- n < 2^30
def isqrt (r : Nat) (n : Source.Expr) : Source.Stmt := s{
  sr := 0;
  sb := 16384;
  while 0 < sb do
    if (sr + sb) * (sr + sb) < !(n) + 1 then
      sr := sr + sb;
    end
    sb := sb >> 1;
  end
  r := sr;
}

-- 1 季節 4096 tick。季節 si から sj へ、割合 sw（0..256）
def season (ticks : Source.Expr) : Source.Stmt := s{
  sp := !(ticks) - (!(ticks) >> 14) * 16384;
  si := sp >> 12;
  sf := sp - si * 4096 - 2458;
  if sf < 0 then
    sf := 0;
  end
  sf := sf * 160 >> 10;
  if 256 < sf then
    sf := 256;
  end
  sw := sf * sf * (768 - 2 * sf) >> 16;
  sj := si + 1 - ((si + 1) >> 2) * 4;
}

def pickFrom (o idx k : Nat) : List Int → Source.Stmt
  | [] => .skip
  | [v] => .assign o (lit v)
  | v :: vs => .ifElse (.binOp .ltS (.var idx) (lit (k + 1))) (.assign o (lit v)) (pickFrom o idx (k + 1) vs)

def pick (o idx : Nat) (vs : List Int) : Source.Stmt := pickFrom o idx 0 vs

-- 季節ごとの値 [春, 夏, 秋, 冬] を補間
def blend (o : Nat) (vs : List Int) : Source.Stmt := s{
  !(pick b1 si vs);
  !(pick b2 sj vs);
  o := b1 + ((b2 - b1) * sw >> 8);
}

def blendRGB (r g b : Nat) (vs : List (Int × Int × Int)) : Source.Stmt := s{
  !(blend r (vs.map (·.1)));
  !(blend g (vs.map (·.2.1)));
  !(blend b (vs.map (·.2.2)));
}

def setRGB (c : Int × Int × Int) : Source.Stmt := s{
  cr := !(lit c.1);
  cg := !(lit c.2.1);
  cb := !(lit c.2.2);
}

def clampV (v : Nat) (lo hi : Int) : Source.Stmt := s{
  if v < !(lit lo) then
    v := !(lit lo);
  end
  if !(lit hi) < v then
    v := !(lit hi);
  end
}

def pack : Source.Stmt := s{
  !(clampV cr 0 255);
  !(clampV cg 0 255);
  !(clampV cb 0 255);
  out := cr * 65536 + cg * 256 + cb;
}

def grass : List (Int × Int × Int) := [(140, 200, 90), (70, 150, 60), (190, 160, 70), (235, 240, 248)]
def shore : List (Int × Int × Int) := [(200, 185, 140), (200, 185, 140), (190, 170, 120), (235, 240, 248)]
def lake : List (Int × Int × Int) := [(70, 150, 210), (30, 120, 200), (30, 90, 160), (205, 228, 242)]
def conifer : List (Int × Int × Int) := [(40, 105, 65), (30, 95, 55), (35, 90, 55), (190, 205, 215)]
def decidA : List (Int × Int × Int) := [(250, 185, 205), (55, 135, 60), (225, 80, 40), (120, 95, 80)]
def decidB : List (Int × Int × Int) := [(245, 215, 225), (75, 150, 55), (240, 160, 40), (140, 115, 95)]
def skyTop : List (Int × Int × Int) := [(90, 150, 225), (40, 110, 220), (70, 110, 170), (120, 140, 170)]
def skyHor : List (Int × Int × Int) := [(245, 215, 225), (200, 230, 250), (250, 205, 150), (225, 230, 238)]

def pentCos : List Int := [256, 79, -207, -207, 79]
def pentSin : List Int := [0, 243, 150, -150, -243]
def hexCos : List Int := [256, 128, -128, -256, -128, 128]
def hexSin : List Int := [0, 222, 222, 0, -222, -222]
def hex30Cos : List Int := [222, 0, -222, -222, 0, 222]
def hex30Sin : List Int := [128, 256, 128, -128, -256, -128]

-- mode 0：地形の高さ（a0, a1 = x, z）。湖面は 0
def mTerrain : Source.Stmt := s{
  !(terrain out e{a0} e{a1});
  if out < 0 then
    out := 0;
  end
}

-- a0..a2 = 点、a3..a5 = カメラ、a6..a9 = cos/sin（ヨー、ピッチ、1/4096 単位）
def camXform : Source.Stmt := s{
  m0 := a0 - a3;
  m1 := a1 - a4;
  m2 := a2 - a5;
  m3 := (m0 * a6 - m2 * a7) >> 12;
  m4 := (m0 * a7 + m2 * a6) >> 12;
  m5 := (m1 * a8 + m4 * a9) >> 12;
  m6 := (m4 * a8 - m1 * a9) >> 12;
}

-- mode 1：画面座標（1/4 画素単位、x と y を 16 ビットずつ詰める）
def mProject : Source.Stmt := s{
  !(camXform);
  if m6 < 77 then
    m6 := 77;
  end
  !(divide m7 e{9338880} e{m6} 24);
  m8 := 1920 + (m3 * m7 >> 12);
  m9 := 1200 - (m5 * m7 >> 12);
  !(clampV m8 (-32000) 32000);
  !(clampV m9 (-32000) 32000);
  out := (m8 + 32768) * 65536 + (m9 + 32768);
}

-- mode 2：奥行き
def mDepth : Source.Stmt := s{
  !(camXform);
  out := m6;
}

-- a10 = 材質（0 地面、2 針葉樹、3・4 広葉樹、5 幹）、a9 = 平均の高さ、a13 = 最高の高さ
def materialColor : Source.Stmt := s{
  if a10 < 1 then
    if a13 < 1 then
      !(blendRGB cr cg cb lake);
    else
      !(hash32 m14 e{a0 >> 7} e{a2 >> 7} nht);
      !(blend m15 [1152, 1664, 1344, -768]);
      m15 := m15 + ((m14 - 512) >> 3);
      if m15 < a9 then
        !(setRGB (242, 245, 250));
      else
        if a9 < 102 then
          !(blendRGB cr cg cb shore);
        else
          if a9 < 1024 then
            !(blendRGB cr cg cb grass);
          else
            !(setRGB (130, 122, 112));
          end
        end
      end
    end
  else
    if a10 < 3 then
      !(blendRGB cr cg cb conifer);
    else
      if a10 < 4 then
        !(blendRGB cr cg cb decidA);
      else
        if a10 < 5 then
          !(blendRGB cr cg cb decidB);
        else
          !(setRGB (90, 65, 50));
        end
      end
    end
  end
}

-- mode 3：面の色（a0..a8 = 3 頂点、a11 = 奥行き、a12 = tick）
def mShade : Source.Stmt := s{
  !(season e{a12});
  m0 := a3 - a0;
  m1 := a4 - a1;
  m2 := a5 - a2;
  m3 := a6 - a0;
  m4 := a7 - a1;
  m5 := a8 - a2;
  m6 := (m1 * m5 - m2 * m4) >> 3;
  m7 := (m2 * m3 - m0 * m5) >> 3;
  m8 := (m0 * m4 - m1 * m3) >> 3;
  if m7 < 0 then
    m6 := 0 - m6;
    m7 := 0 - m7;
    m8 := 0 - m8;
  end
  !(blend m9 [-143, -124, -153, -168]);
  !(blend m10 [157, 186, 137, 94]);
  m11 := m6 * m9 + m7 * m10 + m8 * m9;
  !(isqrt m12 e{m6 * m6 + m7 * m7 + m8 * m8});
  if m12 < 1 then
    m12 := 1;
  end
  m13 := 0;
  if 0 < m11 then
    !(divide m13 e{m11} e{m12} 31);
  end
  if 256 < m13 then
    m13 := 256;
  end
  m13 := 115 + (159 * m13 >> 8);
  !(materialColor);
  cr := cr * m13 >> 8;
  cg := cg * m13 >> 8;
  cb := cb * m13 >> 8;
  !(clampV cr 0 255);
  !(clampV cg 0 255);
  !(clampV cb 0 255);
  !(blendRGB hr hg hb skyHor);
  m14 := a11 * 1567 >> 16;
  !(clampV m14 0 256);
  m14 := (m14 * 102 + (m14 * m14 >> 8) * 154) >> 8;
  cr := cr + ((hr - cr) * m14 >> 8);
  cg := cg + ((hg - cg) * m14 >> 8);
  cb := cb + ((hb - cb) * m14 >> 8);
  !(pack);
}

-- mode 4：空の色（a0 = 0 天頂 / 1 地平線、a1 = tick）
def mSky : Source.Stmt := s{
  !(season e{a1});
  if a0 < 1 then
    !(blendRGB cr cg cb skyTop);
  else
    !(blendRGB cr cg cb skyHor);
  end
  !(pack);
}

-- mode 5：木の根元の高さ（a0, a1 = 区画）。木が無ければ -2^20
def mTreeBase : Source.Stmt := s{
  !(hash32 m0 e{a0 * 3} e{a1 * 5} nht);
  out := 0 - 1048576;
  if m0 < 230 then
    m3 := a0 + a1;
    m3 := (m3 - (m3 >> 1) * 2) * 256;
    !(terrain m1 e{a0 * 256 + m3} e{a1 * 256});
    !(terrain m2 e{a0 * 256 + 256 - m3} e{a1 * 256 + 256});
    if m1 < 0 then
      m1 := 0;
    end
    if m2 < 0 then
      m2 := 0;
    end
    m1 := (m1 + m2) >> 1;
    if (154 < m1) * (m1 < 1280) then
      out := m1;
    end
  end
}

-- mode 6：木の種類（1 針葉樹、2・3 広葉樹）
def mTreeKind : Source.Stmt := s{
  !(hash32 m0 e{a0 * 11} e{a1 * 13} nht);
  if (m0 < 600) * (a2 < 768) then
    out := 2 + m0 - (m0 >> 1) * 2;
  else
    out := 1;
  end
}

-- mode 7：木の頂点（a2 = 根元、a3 = 種類、a4 = 頂点番号、a5 = 成分、a6 = tick）
def mTreeVertex : Source.Stmt := s{
  !(hash32 m3 e{a0 * 17} e{a1 * 19} nht);
  m3 := 205 + (m3 >> 3);
  if a3 < 2 then
    m4 := 5 < a4;
    m5 := a4 - m4 * 6;
    if 4 < m5 then
      m0 := 0;
      m2 := 0;
      m1 := 282 + m4 * 179;
    else
      !(pick m6 m5 pentCos);
      !(pick m7 m5 pentSin);
      m8 := 108 - m4 * 31;
      m0 := m6 * m8 >> 8;
      m2 := m7 * m8 >> 8;
      m1 := 38 + m4 * 154;
    end
  else
    !(season e{a6});
    !(blend m4 [235, 256, 240, 0]);
    m4 := 128 * m4 >> 8;
    m5 := 141 + (m4 >> 1);
    m0 := 0;
    m2 := 0;
    if a4 < 8 then
      m6 := a4 >> 2;
      m7 := a4 - m6 * 4;
      m0 := 18 * ((0 < m7) * (m7 < 3) * 2 - 1);
      m2 := 18 * ((1 < m7) * 2 - 1);
      m1 := m6 * 192;
    else
      if a4 < 9 then
        m1 := m5 + (m4 * 218 >> 8);
      else
        if a4 < 15 then
          m9 := a4 - 9;
          !(pick m6 m9 hexCos);
          !(pick m7 m9 hexSin);
          m8 := m4 * 236 >> 8;
          m0 := m6 * m8 >> 8;
          m2 := m7 * m8 >> 8;
          m1 := m5 + (m4 * 90 >> 8);
        else
          if a4 < 21 then
            m9 := a4 - 15;
            !(pick m6 m9 hex30Cos);
            !(pick m7 m9 hex30Sin);
            m8 := m4 * 225 >> 8;
            m0 := m6 * m8 >> 8;
            m2 := m7 * m8 >> 8;
            m1 := m5 - (m4 * 77 >> 8);
          else
            m1 := m5 - (m4 * 179 >> 8);
          end
        end
      end
    end
  end
  if a5 < 1 then
    out := a0 * 256 + 128 + (m0 * m3 >> 8);
  else
    if a5 < 2 then
      out := a2 + (m1 * m3 >> 8);
    else
      out := a1 * 256 + 128 + (m2 * m3 >> 8);
    end
  end
}

-- mode 8：雪の位置（a0 = 番号、a1 = 成分、a2 = tick、a3..a5 = カメラ）
def mSnow : Source.Stmt := s{
  if a1 < 1 then
    !(hash32 m0 e{a0} e{1} nht);
    !(noise nv e{a0 * 256 + (a2 >> 1)} e{a0 * 37} 8);
    m1 := m0 * 4 + ((nv - 512) >> 2) + (a2 * 3 >> 4) - a3;
    out := a3 - 2048 + m1 - (m1 >> 12) * 4096;
  else
    if a1 < 2 then
      !(hash32 m0 e{a0} e{1} nht);
      !(hash32 m0 e{m0 * 7 + a0} e{2} nht);
      m1 := m0 * 2 - (a2 * 3 >> 2);
      out := a4 - 1280 + m1 - (m1 >> 11) * 2048;
    else
      !(hash32 m0 e{a0} e{1} nht);
      !(hash32 m0 e{m0 * 13 + a0} e{3} nht);
      m1 := m0 * 4 - a5;
      out := a5 - 1024 + m1 - (m1 >> 12) * 4096;
    end
  end
}

-- mode 9：雪の量
def mSnowAmount : Source.Stmt := s{
  !(season e{a0});
  !(blend out [0, 0, 0, 900]);
}

-- mode 10：地形の高さの上界（カメラの高度用）
def mAltitude : Source.Stmt := s{
  !(noise nv e{a0 >> 4} e{a1 >> 4} 8);
  out := (nv * 2 + 1535 - 1350) * 328 >> 8;
}

def dispatch : List Source.Stmt → Nat → Source.Stmt
  | [], _ => .skip
  | [st], _ => st
  | st :: sts, k => .ifElse (.binOp .ltS (.var mode) (lit (k + 1))) st (dispatch sts (k + 1))

def prog : Source.Stmt :=
  dispatch [mTerrain, mProject, mDepth, mShade, mSky, mTreeBase, mTreeKind,
    mTreeVertex, mSnow, mSnowAmount, mAltitude] 0

end Seasons
