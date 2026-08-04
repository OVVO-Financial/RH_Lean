# Exact anchor-coverage scan through 29#

Recorded output of `block_scan.c` (gcc -O2, single run over every integer up to
`29# = 6469693230`). Reproduce with `gcc -O2 -o block_scan block_scan.c -lm && ./block_scan`.

## Mertens and squarefree counts at primorial endpoints

| endpoint | M | Q | expected M | status |
|---|---:|---:|---:|---|
| 2# | 0 | 2 | 0 | ok |
| 3# | -1 | 5 | -1 | ok |
| 5# | -3 | 19 | -3 | ok |
| 7# | -1 | 129 | -1 | ok |
| 11# | -1 | 1405 | -1 | ok |
| 13# | 16 | 18262 | 16 | ok |
| 17# | -25 | 310347 | -25 | ok |
| 19# | 278 | 5896728 | 278 | ok |
| 23# | 3516 | 135624240 | 3516 | ok |
| 29# | -5012 | 3933101824 | -5012 | ok |

## Consecutive endpoint sign products

| pair | M(prev)*M(next) | anchor pair |
|---|---:|---|
| 2# x 3# | 0 | opposite: total coverage |
| 3# x 5# | 3 | same sign: gap case |
| 5# x 7# | 3 | same sign: gap case |
| 7# x 11# | 1 | same sign: gap case |
| 11# x 13# | -16 | opposite: total coverage |
| 13# x 17# | -400 | opposite: total coverage |
| 17# x 19# | -6950 | opposite: total coverage |
| 19# x 23# | 977448 | same sign: gap case |
| 23# x 29# | -17622192 | opposite: total coverage |

## Block (17#, 19#]

  anchors            M(L) = -25   M(U) = 278   product = -6950
  K_*                0.536418786646 at x = 1066854  (M = 432, Q = 648574)
  trough             M = -1078 at x = 7109110
  crest              M = 1060 at x = 6481601
  two endpoints      covered 9189181   uncovered 0
                     K_anchor = 1.026583968026 at x = 603151   (K_anchor/K_* = 1.913773)
  all frozen ends    covered 9189181   uncovered 0
                     K_anchor = 0.536418786646 at x = 1066854   (K_anchor/K_* = 1.000000)

## Block (19#, 23#]

  anchors            M(L) = 278   M(U) = 3516   product = 977448
  K_*                0.595311149129 at x = 179919749  (M = -6226, Q = 109378056)
  trough             M = -6226 at x = 179919749
  crest              M = 5971 at x = 220260118
  two endpoints      covered 205459892   uncovered 7933289
                     K_anchor = 1.968097029386 at x = 9699691   (K_anchor/K_* = 3.305997)
  all frozen ends    covered 213393181   uncovered 0
                     K_anchor = 0.595311149129 at x = 179919749   (K_anchor/K_* = 1.000000)

## Block (23#, 29#]

  anchors            M(L) = 3516   M(U) = -5012   product = -17622192
  K_*                0.590510118734 at x = 1109331447  (M = -15335, Q = 674392719)
  trough             M = -25071 at x = 3773166681
  crest              M = 21791 at x = 5439294781
  two endpoints      covered 6246600361   uncovered 0
                     K_anchor = 1.022394622291 at x = 228044335   (K_anchor/K_* = 1.731375)
  all frozen ends    covered 6246600361   uncovered 0
                     K_anchor = 0.590510118734 at x = 1109331447   (K_anchor/K_* = 1.000000)

## Distinguished prime-2 fibre at the 29# bottleneck x_* = 1109331447

  M = -15335   Q = 674392719   A = -18851   B = 10323
  left  cross -2 M(23#) A = 132560232  (favourable)
  right cross  2 M(29#) B = -103477752  (unfavourable)
  P_2 = -14921.2500   A_2 = 718357949   m_2 = 538768461.7500
  |P_2|/sqrt(m_2) = 0.642841823379    P_2/(M(x_*)-M(23#)) = 0.7915362580
