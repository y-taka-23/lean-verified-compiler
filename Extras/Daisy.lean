import Extras.Syntax

namespace Daisy

-- 32768 Hz、1 拍 = 12288 サンプル、音程は G3 = 0 の半音

def lit (v : Int) : Source.Expr := .lit (BitVec.ofInt 32 v)

def out : Nat := 0
def mode : Nat := 1
def t : Nat := 2
def sS : Nat := 3
def sT : Nat := 4
def sTi : Nat := 5
def aP : Nat := 6
def p1 : Nat := 7
def p2 : Nat := 8
def p3 : Nat := 9
def aC : Nat := 10
def c1 : Nat := 11
def c2 : Nat := 12
def c3 : Nat := 13
def b1 : Nat := 14
def b2 : Nat := 15
def b3 : Nat := 16
def mS : Nat := 17
def mI : Nat := 18
def nS : Nat := 19
def nE : Nat := 20
def i1 : Nat := 21
def iD : Nat := 22
def pS : Nat := 23
def vA : Nat := 24
def rel : Nat := 25
def rst : Nat := 26
def tau : Nat := 27
def u : Nat := 28
def u2 : Nat := 29
def u3 : Nat := 30
def gl : Nat := 31
def ie : Nat := 32
def r : Nat := 33
def w : Nat := 34
def cv : Nat := 35
def ph : Nat := 36
def f1 : Nat := 37
def f2 : Nat := 38
def f3 : Nat := 39
def am : Nat := 40
def x : Nat := 41
def fq : Nat := 42
def fk : Nat := 43
def hp : Nat := 44
def k : Nat := 45
def v : Nat := 46
def a : Nat := 47
def d : Nat := 48
def y : Nat := 49
def h : Nat := 50
def kv : Nat := 51
def sv : Nat := 52
def voice : Nat := 53
def sx : Nat := 54
def sa : Nat := 55
def sy : Nat := 56
def sb : Nat := 57
def rm : Nat := 58
def re : Nat := 59
def r0 : Nat := 60
def rq : Nat := 61
def q : Nat := 62
def bt : Nat := 63
def tau2 : Nat := 64
def br : Nat := 65
def bb : Nat := 66
def q0 : Nat := 67
def q1 : Nat := 68
def q2 : Nat := 69
def q3 : Nat := 70
def env : Nat := 71
def ix : Nat := 72
def mv : Nat := 73
def p : Nat := 74
def acc : Nat := 75

def seqs : List Source.Stmt → Source.Stmt
  | [] => .skip
  | [st] => st
  | st :: sts => .seq st (seqs sts)

def set (o : Nat) (val : Int) : Source.Stmt := .assign o (lit val)

-- キーの昇順に並んだ表から、変数 iv 以下で最大のキーの文を選ぶ二分木
def tree (iv : Nat) : Nat → List (Int × Source.Stmt) → Source.Stmt
  | 0, _ => .skip
  | _, [] => .skip
  | _, [(_, st)] => st
  | fuel + 1, xs =>
    let l := xs.take (xs.length / 2)
    let rs := xs.drop (xs.length / 2)
    match rs with
    | [] => .skip
    | (key, _) :: _ => .ifElse (.binOp .ltS (.var iv) (lit key)) (tree iv fuel l) (tree iv fuel rs)

def table (iv : Nat) (xs : List (Int × Source.Stmt)) : Source.Stmt := tree iv xs.length xs

-- 正弦（位相 32bit → ±32768）
def sinS (o : Nat) (pe : Source.Expr) : Source.Stmt := s{
  sx := !(pe) >> 16;
  sa := sx;
  if sa < 0 then
    sa := 0 - sa;
  end
  sy := sx * (32768 - sa) >> 13;
  sb := sy;
  if sb < 0 then
    sb := 0 - sb;
  end
  o := sy + (((sy * sb >> 15) - sy) * 7373 >> 15);
}

-- 65536 * 256 / xe（256 <= xe < 2^20）
def recip (o : Nat) (xe : Source.Expr) : Source.Stmt := s{
  rm := !(xe);
  re := 0;
  if 65535 < rm then
    rm := rm >> 8;
    re := re + 8;
  end
  if 4095 < rm then
    rm := rm >> 4;
    re := re + 4;
  end
  if 1023 < rm then
    rm := rm >> 2;
    re := re + 2;
  end
  if 511 < rm then
    rm := rm >> 1;
    re := re + 1;
  end
  r0 := 95488 - rm * 128;
  rq := rm * r0 >> 8;
  o := ((r0 >> 2) * (131072 - rq) >> 14) >> re;
}

-- 倍音の周波数 fk（Hz × 1024）でのフォルマント fv の寄与
def formant (fv : Nat) (cB : Int) (g : Int) : Source.Stmt := s{
  d := (fk - fv * 1024) >> 6;
  d := d * !(lit cB) >> 8;
  if (d < 4096) * (0 - 4096 < d) then
    y := d * d >> 8;
    !(recip h e{256 + y});
    a := a + (h >> !(lit g));
  end
}

def kinv : Source.Stmt :=
  table k ((List.range 48).map fun (n : Nat) => (((n : Int) + 1), set kv (65536 / ((n : Int) + 1))))

/-! ## 楽譜 -/

def vowelF : Char → Int × Int × Int
  | 'a' => (730, 1090, 2440)
  | 'i' => (270, 2290, 3010)
  | 'I' => (390, 1990, 2550)
  | 'e' => (480, 1900, 2500)
  | 'E' => (660, 1720, 2410)
  | 'o' => (520, 860, 2410)
  | 'u' => (300, 870, 2240)
  | 'U' => (440, 1020, 2240)
  | _ => (600, 1170, 2390)

-- 子音：長さ、声の大きさ（256 = 1）、フォルマント
def consonant : Char → Int × Int × (Int × Int × Int)
  | 'b' => (500, 20, (220, 800, 2000))
  | 'd' => (500, 20, (220, 1700, 2700))
  | 'g' => (500, 20, (220, 2000, 2400))
  | 'z' => (1500, 77, (250, 1700, 2700))
  | 'v' => (1100, 77, (250, 900, 2300))
  | 'D' => (900, 77, (250, 1500, 2500))
  | 'm' => (1500, 115, (250, 1100, 2300))
  | 'n' => (1400, 115, (250, 1600, 2600))
  | 'l' => (1100, 166, (360, 1100, 2700))
  | 'r' => (1100, 166, (420, 1300, 1600))
  | 'w' => (1000, 154, (300, 700, 2200))
  | _ => (900, 154, (270, 2290, 3010))

structure Note where
  beats : Int
  pitch : Option Int
  onset : List Char := []
  v1 : Char := 'A'
  v2 : Char := 'A'
  coda : List Char := []

def S (beats pitch : Int) (onset : String) (v1 : Char) (v2 : Option Char := none) (coda : String := "") : Note :=
  { beats, pitch := some pitch, onset := onset.toList, v1, v2 := v2.getD v1, coda := coda.toList }

def R (beats : Int) : Note := { beats, pitch := none }

def song : List Note := [
  S 3 7 "d" 'e' 'i', S 3 4 "z" 'i', S 3 0 "d" 'e' 'i', S 2 (-5) "z" 'i', R 1,
  S 1 (-3) "g" 'I' none "v", S 1 (-1) "m" 'i', S 1 0 "y" 'o', S 2 (-3) "" 'E' none "n",
  S 1 0 "zw" 'A', S 5 (-5) "d" 'u', R 1,
  S 3 2 "" 'a' 'i' "m", S 3 7 "" 'E' none "v", S 3 4 "gr" 'e' 'i', S 2 0 "z" 'i', R 1,
  S 1 (-3) "" 'o' none "l", S 1 (-1) "v" 'o', S 1 0 "D" 'A', S 2 2 "l" 'A' none "v",
  S 1 4 "" 'A' none "v", S 5 2 "y" 'u', R 1]

def chords : List (List Int) :=
  let G := [0, 4, 7]
  let C := [5, 9, 12]
  let D7 := [2, 6, 9, 12]
  let Am := [2, 5, 9]
  [G, G, C, G, D7, C, D7, D7, D7, G, G, G, Am, D7, D7, D7]

def beat : Int := 12288

def toInt (f : Float) : Int := (f.round.toUInt64.toNat : Int)

-- 1 サンプルあたりの位相の増分（2^32 で 1 周）
def incOf (n : Int) : Int :=
  toInt (196.0 * Float.pow 2.0 (Float.ofInt n / 12.0) * 131072.0)

-- ビブラート（深さ 0.35 半音、5.5 Hz）による位相の振れ幅 / 2^15
def vibOf (inc : Int) : Int :=
  let depth := Float.pow 2.0 (0.35 / 12.0) - 1.0
  let omega := 2.0 * 3.141592653589793 * 5.5 / 32768.0
  toInt (Float.ofInt inc * depth / omega / 32768.0)

structure Seg where
  start : Int
  rest : Bool
  vals : List (Nat × Int) := []

-- 音符の並びから区間の表を作る
def segments : List Note → Int → Option (Int × Int × (Int × Int × Int)) → Int → List Seg
  | [], _, _, _ => []
  | nt :: more, t0, prev, phase =>
    let len := nt.beats * beat
    match nt.pitch with
    | none => { start := t0, rest := true } :: segments more (t0 + len) none 0
    | some n =>
      let inc := incOf n
      let dInc := match prev with
        | some (pi, _, _) => pi - inc
        | none => 0
      let release := match more with
        | [] => true
        | nx :: _ => nx.pitch.isNone
      let cons := nt.onset.map consonant
      let codas := nt.coda.map fun c => let (l, am, f) := consonant c; (l * 4 / 5, am, f)
      let used := (cons ++ codas).foldl (fun s c => s + c.1) 0
      let vlen := len - used
      -- (長さ, 大きさ, 始まりのフォルマント, 終わりのフォルマント, 母音か)
      let parts := cons.map (fun (l, am, f) => (l, am, f, f, false)) ++
        [(vlen, 256, vowelF nt.v1, vowelF nt.v2, true)] ++
        codas.map (fun (l, am, f) => (l, am, f, f, false))
      let rec go (ps : List (Int × Int × (Int × Int × Int) × (Int × Int × Int) × Bool))
          (s : Int) (first : Bool) (pa : Int) (pf : Int × Int × Int) : List Seg :=
        match ps with
        | [] => []
        | (l, am, cf, bf, vw) :: rest =>
          let tr := min l (if first then 700 else if vw then 1400 else 700)
          let (pa', pf') := if first then
              match prev with
              | some (_, ea, ef) => (ea, ef)
              | none => (0, cf)
            else (pa, pf)
          let (ms, mi) := if vw then (s + l * 55 / 100, 6553600 / (45 * l)) else (s + l, 0)
          let seg : Seg := { start := s, rest := false, vals := [
            (sS, s), (sT, tr), (sTi, 65536 / tr), (aP, pa'),
            (p1, pf'.1), (p2, pf'.2.1), (p3, pf'.2.2), (aC, am),
            (c1, cf.1), (c2, cf.2.1), (c3, cf.2.2), (b1, bf.1), (b2, bf.2.1), (b3, bf.2.2),
            (mS, ms), (mI, mi), (nS, t0), (nE, t0 + len), (i1, inc), (iD, dInc), (pS, phase),
            (vA, vibOf inc), (rel, if release then 1 else 0)] }
          seg :: go rest (s + l) false am bf
      let last := parts.getLast? |>.map (fun (_, am, _, bf, _) => (am, bf)) |>.getD (256, vowelF nt.v2)
      let glide := (Int.fdiv dInc 1024) * 341 * 1024
      go parts t0 true 0 (0, 0, 0) ++
        segments more (t0 + len) (some (inc, last.1, last.2)) (phase + inc * len + glide)

def total : Int := song.foldl (fun s n => s + n.beats * beat) 0

def lookup : Source.Stmt :=
  table t ((segments song 0 none 0).map fun sg =>
    (sg.start, if sg.rest then set rst 1 else seqs (set rst 0 :: sg.vals.map fun (o, val) => set o val)))

def chordTable : Source.Stmt :=
  table br ((chords.zipIdx).map fun (ns, i) =>
    let incs := ns.map incOf ++ [0, 0, 0, 0]
    ((i : Int), seqs [set q0 incs[0]!, set q1 incs[1]!, set q2 incs[2]!, set q3 incs[3]!]))

/-! ## 合成 -/

def voiceS : Source.Stmt := s{
  voice := 0;
  if rst < 1 then
    tau := t - nS;
    if tau < 1024 then
      u := 1024 - tau;
      u2 := u * u >> 10;
      u3 := u2 * u >> 10;
      gl := (iD >> 10) * 341 * (1024 - u3);
      ie := i1 + (iD >> 10) * u2;
    else
      gl := (iD >> 10) * 349184;
      ie := i1;
    end
    r := 0;
    if 6000 < tau then
      r := (tau - 6000) * 33 >> 10;
      if 256 < r then
        r := 256;
      end
    end
    w := (nE - t) * 175 >> 10;
    if w < r then
      r := w;
    end
    !(sinS cv e{t * 720896 + 1073741824});
    ph := pS + i1 * tau + gl + (vA * r >> 8) * cv;
    f1 := c1;
    f2 := c2;
    f3 := c3;
    if mS < t then
      x := (t - mS) * mI;
      if 65536 < x then
        x := 65536;
      end
      f1 := c1 + ((b1 - c1) * x >> 16);
      f2 := c2 + ((b2 - c2) * x >> 16);
      f3 := c3 + ((b3 - c3) * x >> 16);
    end
    am := aC;
    if t - sS < sT then
      x := (t - sS) * sTi;
      f1 := p1 + ((f1 - p1) * x >> 16);
      f2 := p2 + ((f2 - p2) * x >> 16);
      f3 := p3 + ((f3 - p3) * x >> 16);
      am := aP + ((am - aP) * x >> 16);
    end
    if rel then
      w := (nE - t) * 55;
      if w < 65536 then
        am := am * w >> 16;
      end
    end
    fq := ie >> 7;
    fk := fq;
    hp := ph;
    k := 1;
    v := 0;
    while fk < 4608000 do
      a := 0;
      !(formant f1 46 0);
      !(formant f2 34 1);
      !(formant f3 24 2);
      !(kinv);
      w := (a >> 4) * (kv >> 4) >> 8;
      !(sinS sv e{hp});
      v := v + ((w >> 2) * sv >> 15);
      hp := hp + ph;
      fk := fk + fq;
      k := k + 1;
    end
    voice := (v * am >> 8) * 5 >> 2;
  end
}

-- 伴奏の 1 音（FM、変調指数 ixQ / 256、音量 gain / 32768）
def fmNote (inc : Source.Expr) (ixQ gain : Int) : Source.Stmt := s{
  p := tau2 * !(inc);
  !(sinS mv e{p});
  ix := env * !(lit ixQ) >> 14;
  !(sinS sv e{p + (mv * ix >> 8) * 20861});
  acc := acc + ((sv * env >> 14) * !(lit gain) >> 15);
}

-- 3 拍子：1 拍目にベース、2・3 拍目に和音
def accS : Source.Stmt := s{
  q := t >> 12;
  bt := q * 21846 >> 16;
  tau2 := t - bt * 12288;
  br := bt * 21846 >> 16;
  bb := bt - br * 3;
  !(chordTable);
  u := (12288 - tau2) >> 4;
  env := u * u * 1820 >> 16;
  if tau2 < 200 then
    env := env * tau2 * 328 >> 16;
  end
  acc := 0;
  if bb < 1 then
    !(fmNote e{q0 >> 2} 307 15088);
  else
    !(fmNote e{q0} 154 3429);
    !(fmNote e{q1} 154 3429);
    !(fmNote e{q2} 154 3429);
    if 0 < q3 then
      !(fmNote e{q3} 154 3429);
    end
  end
}

-- mode 0：時刻 t のサンプル（±32767）
def mSample : Source.Stmt := s{
  !(lookup);
  !(voiceS);
  !(accS);
  out := voice + acc;
  if 32767 < out then
    out := 32767;
  end
  if out < 0 - 32767 then
    out := 0 - 32767;
  end
}

-- mode 1：曲の長さ（サンプル数）
def mLength : Source.Stmt := set out total

def prog : Source.Stmt :=
  .ifElse (.binOp .ltS (.var mode) (lit 1)) mSample mLength

end Daisy
