REAL_POLY_CONV  `-- &1 +
   (&2 pow 2 *
    ((y1 - x1) * (z2 - x2) * (w3 - x3) +
     (y2 - x2) * (z3 - x3) * (w1 - x1) +
     (y3 - x3) * (z1 - x1) * (w2 - x2) -
     (y1 - x1) * (z3 - x3) * (w2 - x2) -
     (y2 - x2) * (z1 - x1) * (w3 - x3) -
     (y3 - x3) * (z2 - x2) * (w1 - x1)) pow
    2 -
    (((x1 - y1) * (x1 - y1) + (x2 - y2) * (x2 - y2) + (x3 - y3) * (x3 - y3)) *
     ((z1 - w1) * (z1 - w1) + (z2 - w2) * (z2 - w2) + (z3 - w3) * (z3 - w3)) *
     (--((x1 - y1) * (x1 - y1) +
         (x2 - y2) * (x2 - y2) +
         (x3 - y3) * (x3 - y3)) +
      ((x1 - z1) * (x1 - z1) + (x2 - z2) * (x2 - z2) + (x3 - z3) * (x3 - z3)) +
      ((x1 - w1) * (x1 - w1) + (x2 - w2) * (x2 - w2) + (x3 - w3) * (x3 - w3)) -
      ((z1 - w1) * (z1 - w1) + (z2 - w2) * (z2 - w2) + (z3 - w3) * (z3 - w3)) +
      ((y1 - w1) * (y1 - w1) + (y2 - w2) * (y2 - w2) + (y3 - w3) * (y3 - w3)) +
      (y1 - z1) * (y1 - z1) +
      (y2 - z2) * (y2 - z2) +
      (y3 - z3) * (y3 - z3)) +
     ((x1 - z1) * (x1 - z1) + (x2 - z2) * (x2 - z2) + (x3 - z3) * (x3 - z3)) *
     ((y1 - w1) * (y1 - w1) + (y2 - w2) * (y2 - w2) + (y3 - w3) * (y3 - w3)) *
     (((x1 - y1) * (x1 - y1) + (x2 - y2) * (x2 - y2) + (x3 - y3) * (x3 - y3)) -
      ((x1 - z1) * (x1 - z1) + (x2 - z2) * (x2 - z2) + (x3 - z3) * (x3 - z3)) +
      ((x1 - w1) * (x1 - w1) + (x2 - w2) * (x2 - w2) + (x3 - w3) * (x3 - w3)) +
      ((z1 - w1) * (z1 - w1) + (z2 - w2) * (z2 - w2) + (z3 - w3) * (z3 - w3)) -
      ((y1 - w1) * (y1 - w1) + (y2 - w2) * (y2 - w2) + (y3 - w3) * (y3 - w3)) +
      (y1 - z1) * (y1 - z1) +
      (y2 - z2) * (y2 - z2) +
      (y3 - z3) * (y3 - z3)) +
     ((x1 - w1) * (x1 - w1) + (x2 - w2) * (x2 - w2) + (x3 - w3) * (x3 - w3)) *
     ((y1 - z1) * (y1 - z1) + (y2 - z2) * (y2 - z2) + (y3 - z3) * (y3 - z3)) *
     (((x1 - y1) * (x1 - y1) + (x2 - y2) * (x2 - y2) + (x3 - y3) * (x3 - y3)) +
      ((x1 - z1) * (x1 - z1) + (x2 - z2) * (x2 - z2) + (x3 - z3) * (x3 - z3)) -
      ((x1 - w1) * (x1 - w1) + (x2 - w2) * (x2 - w2) + (x3 - w3) * (x3 - w3)) +
      ((z1 - w1) * (z1 - w1) + (z2 - w2) * (z2 - w2) + (z3 - w3) * (z3 - w3)) +
      ((y1 - w1) * (y1 - w1) + (y2 - w2) * (y2 - w2) + (y3 - w3) * (y3 - w3)) -
      ((y1 - z1) * (y1 - z1) + (y2 - z2) * (y2 - z2) + (y3 - z3) * (y3 - z3))) -
     ((x1 - z1) * (x1 - z1) + (x2 - z2) * (x2 - z2) + (x3 - z3) * (x3 - z3)) *
     ((x1 - w1) * (x1 - w1) + (x2 - w2) * (x2 - w2) + (x3 - w3) * (x3 - w3)) *
     ((z1 - w1) * (z1 - w1) + (z2 - w2) * (z2 - w2) + (z3 - w3) * (z3 - w3)) -
     ((x1 - y1) * (x1 - y1) + (x2 - y2) * (x2 - y2) + (x3 - y3) * (x3 - y3)) *
     ((x1 - w1) * (x1 - w1) + (x2 - w2) * (x2 - w2) + (x3 - w3) * (x3 - w3)) *
     ((y1 - w1) * (y1 - w1) + (y2 - w2) * (y2 - w2) + (y3 - w3) * (y3 - w3)) -
     ((x1 - y1) * (x1 - y1) + (x2 - y2) * (x2 - y2) + (x3 - y3) * (x3 - y3)) *
     ((x1 - z1) * (x1 - z1) + (x2 - z2) * (x2 - z2) + (x3 - z3) * (x3 - z3)) *
     ((y1 - z1) * (y1 - z1) + (y2 - z2) * (y2 - z2) + (y3 - z3) * (y3 - z3)) -
     ((z1 - w1) * (z1 - w1) + (z2 - w2) * (z2 - w2) + (z3 - w3) * (z3 - w3)) *
     ((y1 - w1) * (y1 - w1) + (y2 - w2) * (y2 - w2) + (y3 - w3) * (y3 - w3)) *
     ((y1 - z1) * (y1 - z1) + (y2 - z2) * (y2 - z2) + (y3 - z3) * (y3 - z3)))) *
   z`
