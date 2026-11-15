;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/div_Div_div_sb_qrqtvc: the verification condition
;; for schoolbook multi-precision quotient/remainder division, including
;; reciprocal estimation, mutable pointer/array updates, loop invariants,
;; correction steps, and the final quotient/remainder bounds. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defconst *dsq-radix* 18446744073709551616)
(defconst *dsq-bv32-modulus* 4294967296)
(defconst *dsq-bv32-sign* 2147483648)

(defun dsq-bv64-p (x)
  (and (integerp x) (<= 0 x) (< x *dsq-radix*)))

(defun dsq-bv32-p (x)
  (and (integerp x) (<= 0 x) (< x *dsq-bv32-modulus*)))

(defun dsq-sint32 (x)
  (if (< x *dsq-bv32-sign*) x (- x *dsq-bv32-modulus*)))

(defun dsq-int32-in-bounds-p (x)
  (and (integerp x)
       (<= (- *dsq-bv32-sign*) x)
       (<= x (- *dsq-bv32-sign* 1))))

(defun dsq-uint64-in-bounds-p (x)
  (and (integerp x) (<= 0 x) (< x *dsq-radix*)))

(defun dsq-ipow (base exponent)
  (expt base (nfix exponent)))

(defun dsq-bv64-list-p (xs)
  (if (consp xs)
      (and (dsq-bv64-p (car xs))
           (dsq-bv64-list-p (cdr xs)))
    (equal xs nil)))

;; The Why3 C pointer record is rendered by its complete statement-observable
;; tuple (data, offset, min, max, writable, zone); record equality is therefore
;; structural equality of this tagged tuple.

(defun dsq-ptr-p (p)
  (and (true-listp p)
       (equal (len p) 7)
       (equal (nth 0 p) :dsq-ptr)
       (dsq-bv64-list-p (nth 1 p))
       (integerp (nth 2 p))
       (integerp (nth 3 p))
       (integerp (nth 4 p))
       (booleanp (nth 5 p))))

(defun dsq-data (p) (nth 1 p))
(defun dsq-offset (p) (nth 2 p))
(defun dsq-min (p) (nth 3 p))
(defun dsq-max (p) (nth 4 p))
(defun dsq-writable (p) (nth 5 p))
(defun dsq-zone (p) (nth 6 p))

(defun dsq-nth-default (xs index default)
  (let ((tail (nthcdr (nfix index) xs)))
    (if (consp tail) (car tail) default)))

(defun dsq-map-base (p)
  (list :base p))

(defun dsq-map-update (map index value)
  (list :update map index value))

(defun dsq-map-p (map)
  (declare (xargs :measure (acl2-count map)))
  (or (and (true-listp map)
           (equal (len map) 2)
           (equal (car map) :base)
           (dsq-ptr-p (cadr map)))
      (and (true-listp map)
           (equal (len map) 4)
           (equal (car map) :update)
           (dsq-map-p (cadr map))
           (integerp (caddr map))
           (dsq-bv64-p (cadddr map)))))

(defun dsq-map-get (map index)
  (declare (xargs :measure (acl2-count map)))
  (if (and (consp map) (equal (car map) :update))
      (if (equal index (caddr map))
          (cadddr map)
        (dsq-map-get (cadr map) index))
    (if (< index 0)
        0
      (let* ((p (cadr map))
             (v (nth (nfix index) (dsq-data p))))
        (if (dsq-bv64-p v) v 0)))))

(defun-sk dsq-map-equal-p (left right)
  (forall (index)
    (implies (integerp index)
             (equal (dsq-map-get left index)
                    (dsq-map-get right index)))))

(defun dsq-valid-p (p size)
  (and (dsq-int32-in-bounds-p size)
       (<= 0 size)
       (<= 0 (dsq-min p))
       (<= (dsq-min p) (dsq-offset p))
       (<= (+ (dsq-offset p) size) (dsq-max p))
       (<= (dsq-max p) (len (dsq-data p)))))

(defun dsq-value-sub-count (map index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (dsq-map-get map index)
       (* *dsq-radix*
          (dsq-value-sub-count map (+ index 1) (- count 1))))))

(defun dsq-value-sub (map start end)
  (dsq-value-sub-count map start (nfix (- end start))))

(defun dsq-value (p size)
  (dsq-value-sub (dsq-map-base p)
                 (dsq-offset p)
                 (+ (dsq-offset p) size)))

(defun dsq-normalized-p (p size-word)
  (let ((size (dsq-sint32 size-word)))
    (and (dsq-valid-p p size)
         (<= (floor *dsq-radix* 2)
             (dsq-map-get (dsq-map-base p)
                          (- (+ (dsq-offset p) size) 1))))))

(defun dsq-reciprocal-3by2-p (v dh dl)
  (equal v
         (- (floor (- (* *dsq-radix* *dsq-radix* *dsq-radix*) 1)
                   (+ dl (* *dsq-radix* dh)))
            *dsq-radix*)))

(defun dsq-compare-int (x y)
  (if (< x y) -1 (if (equal x y) 0 1)))
(defun-sk dsq-q1-p (sy y xd qh)
  (forall (o8)
    (implies (booleanp o8) (implies (and (implies (equal qh 0) (equal o8 t)) (implies (equal o8 t) (equal qh 0))) (implies (equal (not o8) t) (and (and (and (<= 0 (dsq-sint32 sy)) (dsq-valid-p xd (dsq-sint32 sy))) (dsq-valid-p y (dsq-sint32 sy))) (equal (dsq-writable xd) t)))))))

(defun-sk dsq-q2-p (sy xd xd1)
  (forall (j)
    (implies (integerp j) (implies (or (< j (dsq-offset xd1)) (<= (+ (dsq-offset xd1) (dsq-sint32 sy)) j)) (equal (dsq-map-get (dsq-map-base xd1) j) (dsq-map-get (dsq-map-base xd) j))))))

(defun-sk dsq-q3-p (sy y xd xd1)
  (exists (b)
    (and (dsq-bv64-p b) (and (and (equal (- (dsq-value xd1 (dsq-sint32 sy)) (* (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 sy)) b)) (- (dsq-value xd (dsq-sint32 sy)) (dsq-value y (dsq-sint32 sy)))) (and (<= 0 b) (<= b 1))) (dsq-q2-p sy xd xd1)))))

(defun-sk dsq-q4-p (sy x y o2 xd x1 xp)
  (exists (xd1)
    (and (dsq-ptr-p xd1) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (equal (dsq-data xd1) (dsq-data x1)) (equal (len (dsq-data x1)) (len (dsq-data xd)))) (equal (dsq-offset xd1) (dsq-offset xd))) (equal (dsq-min xd1) (dsq-min xd))) (equal (dsq-max xd1) (dsq-max xd))) (equal (dsq-writable xd1) (dsq-writable xd))) (equal (dsq-zone xd1) (dsq-zone xd))) (and (and (and (and (and (and (equal (dsq-data xp) (dsq-data x1)) (equal (len (dsq-data x1)) (len (dsq-data o2)))) (equal (dsq-offset xp) (dsq-offset o2))) (equal (dsq-min xp) (dsq-min o2))) (equal (dsq-max xp) (dsq-max o2))) (equal (dsq-writable xp) (dsq-writable o2))) (equal (dsq-zone xp) (dsq-zone o2)))) (equal (len (dsq-data x1)) (len (dsq-data x)))) (equal (dsq-offset x1) (dsq-offset x))) (equal (dsq-min x1) (dsq-min x))) (equal (dsq-max x1) (dsq-max x))) (equal (dsq-writable x1) (dsq-writable x))) (equal (dsq-zone x1) (dsq-zone x))) (dsq-q3-p sy y xd xd1)))))

(defun-sk dsq-q5-p (sy x y o2 xd qh x1 xp)
  (exists (o8)
    (and (booleanp o8) (and (and (implies (equal qh 0) (equal o8 t)) (implies (equal o8 t) (equal qh 0))) (if (equal (not o8) t) (dsq-q4-p sy x y o2 xd x1 xp) (and (equal x1 x) (equal xp o2)))))))

(defun-sk dsq-q6-p (o12 xc)
  (forall (i1)
    (implies (integerp i1) (implies (and (<= 0 i1) (< i1 (len xc))) (equal (dsq-nth-default xc (nfix i1) 0) (dsq-nth-default o12 (nfix i1) 0))))))

(defun-sk dsq-q7-p (sy xd1 xd2)
  (forall (j)
    (implies (integerp j) (implies (or (< j (dsq-offset xd2)) (<= (+ (dsq-offset xd2) (dsq-sint32 sy)) j)) (equal (dsq-map-get (dsq-map-base xd2) j) (dsq-map-get (dsq-map-base xd1) j))))))

(defun-sk dsq-q8-p (sy sx x dh dl mdn vy qh i q1 o8 xp2 x3 o17)
  (forall (qp1 q2)
    (implies (and (dsq-ptr-p qp1) (dsq-ptr-p q2)) (implies (and (and (and (and (and (and (equal (dsq-data qp1) (dsq-data q2)) (equal (len (dsq-data q2)) (len (dsq-data o17)))) (equal (dsq-offset qp1) (dsq-offset o17))) (equal (dsq-min qp1) (dsq-min o17))) (equal (dsq-max qp1) (dsq-max o17))) (equal (dsq-writable qp1) (dsq-writable o17))) (equal (dsq-zone qp1) (dsq-zone o17))) (implies (and (and (and (and (and (and (equal (dsq-data qp1) (dsq-data q2)) (equal (len (dsq-data q2)) (len (dsq-data o17)))) (equal (dsq-offset qp1) (dsq-offset o17))) (equal (dsq-min qp1) (dsq-min o17))) (equal (dsq-max qp1) (dsq-max o17))) (equal (dsq-writable qp1) (dsq-writable o17))) (equal (dsq-zone qp1) (dsq-zone o17))) (implies (and (and (and (and (and (equal (len (dsq-data q2)) (len (dsq-data q1))) (equal (dsq-offset q2) (dsq-offset q1))) (equal (dsq-min q2) (dsq-min q1))) (equal (dsq-max q2) (dsq-max q1))) (equal (dsq-writable q2) (dsq-writable q1))) (equal (dsq-zone q2) (dsq-zone q1))) (implies (dsq-map-equal-p (dsq-map-base qp1) (dsq-map-update (dsq-map-base o17) (dsq-offset qp1) 18446744073709551615)) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (< (dsq-sint32 o8) (dsq-sint32 i)) (and (<= 0 (dsq-sint32 o8)) (<= (dsq-sint32 o8) (- (dsq-sint32 sx) (dsq-sint32 sy))))) (equal (dsq-offset qp1) (+ (dsq-offset q2) (dsq-sint32 o8)))) (equal (dsq-offset xp2) (- (+ (+ (dsq-offset x3) (dsq-sint32 sy)) (dsq-sint32 o8)) 2))) (equal (len (dsq-data qp1)) (len (dsq-data q2)))) (equal (dsq-min qp1) (dsq-min q2))) (equal (dsq-max qp1) (dsq-max q2))) (equal (len (dsq-data xp2)) (len (dsq-data x3)))) (equal (dsq-min xp2) (dsq-min x3))) (equal (dsq-max xp2) (dsq-max x3))) (dsq-map-equal-p (dsq-map-base qp1) (dsq-map-base q2))) (dsq-map-equal-p (dsq-map-base xp2) (dsq-map-base x3))) (and (equal (dsq-writable qp1) t) (equal (dsq-writable xp2) t))) (equal (dsq-value x (dsq-sint32 sx)) (+ (+ (* (* (+ (dsq-value qp1 (- (- (dsq-sint32 sx) (dsq-sint32 sy)) (dsq-sint32 o8))) (* qh (dsq-ipow (+ 18446744073709551615 1) (- (- (dsq-sint32 sx) (dsq-sint32 sy)) (dsq-sint32 o8))))) vy) (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 o8))) (dsq-value x3 (- (+ (dsq-sint32 sy) (dsq-sint32 o8)) 1))) (* (dsq-ipow (+ 18446744073709551615 1) (- (+ (dsq-sint32 sy) (dsq-sint32 o8)) 1)) (dsq-map-get (dsq-map-base xp2) (+ (dsq-offset xp2) 1)))))) (< (+ (dsq-value-sub (dsq-map-base x3) (+ (dsq-offset xp2) (dsq-sint32 mdn)) (- (+ (+ (dsq-offset xp2) (dsq-sint32 mdn)) (dsq-sint32 sy)) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) (dsq-map-get (dsq-map-base xp2) (+ (dsq-offset xp2) 1)))) vy)) (<= (+ (dsq-map-get (dsq-map-base x3) (dsq-offset xp2)) (* (+ 18446744073709551615 1) (dsq-map-get (dsq-map-base xp2) (+ (dsq-offset xp2) 1)))) (+ dl (* (+ 18446744073709551615 1) dh)))))))))))

(defun-sk dsq-q9-p (sy sx x dh dl mdn vy qh i qp q1 o8 xp2 x3)
  (forall (o17)
    (implies (dsq-ptr-p o17) (implies (and (and (and (and (and (and (and (equal (dsq-offset o17) (+ (dsq-offset qp) (- 1))) (equal (len (dsq-data o17)) (len (dsq-data qp)))) (dsq-map-equal-p (dsq-map-base o17) (dsq-map-base qp))) (equal (dsq-data o17) (dsq-data qp))) (equal (dsq-min o17) (dsq-min qp))) (equal (dsq-max o17) (dsq-max qp))) (equal (dsq-zone o17) (dsq-zone qp))) (equal (dsq-writable o17) (dsq-writable qp))) (let ((o18 (- (- (+ (dsq-offset o17) (dsq-sint32 sx)) (dsq-sint32 sy)) (dsq-sint32 o8)))) (let ((o19 (+ (dsq-offset o17) 1))) (let ((o20 (dsq-offset o17))) (let ((o21 (dsq-map-base q1))) (and (and (<= o19 o18) (or (< o20 o19) (<= o18 o20))) (implies (equal (dsq-value-sub o21 o19 o18) (dsq-value-sub (dsq-map-update o21 o20 18446744073709551615) o19 o18)) (and (and (and (<= (dsq-min o17) (dsq-offset o17)) (< (dsq-offset o17) (dsq-max o17))) (equal (dsq-writable o17) t)) (dsq-q8-p sy sx x dh dl mdn vy qh i q1 o8 xp2 x3 o17))))))))))))

(defun-sk dsq-q10-p (sy sx x y dh dl mdn vy qh i qp x2 q1 o8 xd1 xd2 xp2 x3)
  (forall (b)
    (implies (dsq-bv64-p b) (implies (and (equal (- (dsq-value xd2 (dsq-sint32 sy)) (* (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 sy)) b)) (- (dsq-value xd1 (dsq-sint32 sy)) (* (dsq-value y (dsq-sint32 sy)) 18446744073709551615))) (dsq-q7-p sy xd1 xd2)) (and (equal (dsq-value x3 (dsq-sint32 o8)) (dsq-value x2 (dsq-sint32 o8))) (implies (equal (dsq-value x3 (dsq-sint32 o8)) (dsq-value x2 (dsq-sint32 o8))) (let ((o13 (+ (dsq-offset x3) (- (+ (dsq-sint32 sy) (dsq-sint32 o8)) 1)))) (let ((o14 (dsq-offset xd2))) (let ((o15 (dsq-offset x3))) (let ((o16 (dsq-map-base x3))) (and (and (<= o15 o14) (<= o14 o13)) (implies (equal (dsq-value-sub o16 o15 o13) (+ (dsq-value-sub o16 o15 o14) (* (dsq-value-sub o16 o14 o13) (dsq-ipow (+ 18446744073709551615 1) (- o14 o15))))) (and (and (and (<= (dsq-min xp2) (+ (dsq-offset xp2) 1)) (< (+ (dsq-offset xp2) 1) (dsq-max xp2))) (and (<= (dsq-min qp) (+ (dsq-offset qp) (- 1))) (<= (+ (dsq-offset qp) (- 1)) (dsq-max qp)))) (dsq-q9-p sy sx x dh dl mdn vy qh i qp q1 o8 xp2 x3))))))))))))))

(defun-sk dsq-q11-p (sy sx x y dh dl mdn vy qh i qp x2 q1 o8 o9 xd1)
  (forall (xd2 xp2 x3)
    (implies (and (dsq-ptr-p xd2) (dsq-ptr-p xp2) (dsq-ptr-p x3)) (implies (and (and (and (and (and (and (equal (dsq-data xd2) (dsq-data x3)) (equal (len (dsq-data x3)) (len (dsq-data xd1)))) (equal (dsq-offset xd2) (dsq-offset xd1))) (equal (dsq-min xd2) (dsq-min xd1))) (equal (dsq-max xd2) (dsq-max xd1))) (equal (dsq-writable xd2) (dsq-writable xd1))) (equal (dsq-zone xd2) (dsq-zone xd1))) (implies (and (and (and (and (and (and (equal (dsq-data xp2) (dsq-data x3)) (equal (len (dsq-data x3)) (len (dsq-data o9)))) (equal (dsq-offset xp2) (dsq-offset o9))) (equal (dsq-min xp2) (dsq-min o9))) (equal (dsq-max xp2) (dsq-max o9))) (equal (dsq-writable xp2) (dsq-writable o9))) (equal (dsq-zone xp2) (dsq-zone o9))) (implies (and (and (and (and (and (equal (len (dsq-data x3)) (len (dsq-data x2))) (equal (dsq-offset x3) (dsq-offset x2))) (equal (dsq-min x3) (dsq-min x2))) (equal (dsq-max x3) (dsq-max x2))) (equal (dsq-writable x3) (dsq-writable x2))) (equal (dsq-zone x3) (dsq-zone x2))) (dsq-q10-p sy sx x y dh dl mdn vy qh i qp x2 q1 o8 xd1 xd2 xp2 x3)))))))

(defun-sk dsq-q12-p (sy sx x y dh dl mdn vy qh i qp x2 q1 o8 o9 xd1 o12)
  (forall (xc)
    (implies (dsq-bv64-list-p xc) (implies (and (equal (len xc) (len o12)) (dsq-q6-p o12 xc)) (and (and (and (dsq-valid-p y (dsq-sint32 sy)) (dsq-valid-p xd1 (dsq-sint32 sy))) (equal (dsq-writable xd1) t)) (dsq-q11-p sy sx x y dh dl mdn vy qh i qp x2 q1 o8 o9 xd1))))))

(defun-sk dsq-q13-p (o16 xc)
  (forall (i1)
    (implies (integerp i1) (implies (and (<= 0 i1) (< i1 (len xc))) (equal (dsq-nth-default xc (nfix i1) 0) (dsq-nth-default o16 (nfix i1) 0))))))

(defun-sk dsq-q14-p (xd1 o17 xd2)
  (forall (j)
    (implies (integerp j) (implies (or (< j (dsq-offset xd2)) (<= (+ (dsq-offset xd2) (dsq-sint32 o17)) j)) (equal (dsq-map-get (dsq-map-base xd2) j) (dsq-map-get (dsq-map-base xd1) j))))))

(defun-sk dsq-q15-p (o33 xc1)
  (forall (i1)
    (implies (integerp i1) (implies (and (<= 0 i1) (< i1 (len xc1))) (equal (dsq-nth-default xc1 (nfix i1) 0) (dsq-nth-default o33 (nfix i1) 0))))))

(defun-sk dsq-q16-p (xd3 o34 xd4)
  (forall (j)
    (implies (integerp j) (implies (or (< j (dsq-offset xd4)) (<= (+ (dsq-offset xd4) (dsq-sint32 o34)) j)) (equal (dsq-map-get (dsq-map-base xd4) j) (dsq-map-get (dsq-map-base xd3) j))))))

(defun-sk dsq-q17-p (sy vy o19 xd3 xd4 o35)
  (forall (o36)
    (implies (dsq-bv64-p o36) (implies (equal o36 (mod (+ o19 o35) (+ 18446744073709551615 1))) (equal (+ (dsq-value xd4 (- (dsq-sint32 sy) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) o36)) (- (+ (+ (dsq-value xd3 (- (dsq-sint32 sy) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) o19)) vy) (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 sy))))))))

(defun-sk dsq-q18-p (sy dh vy o19 xd3 xd4 c)
  (forall (o35)
    (implies (dsq-bv64-p o35) (implies (equal o35 (mod (+ dh c) (+ 18446744073709551615 1))) (dsq-q17-p sy vy o19 xd3 xd4 o35)))))

(defun-sk dsq-q19-p (sy sx x dh dl mdn vy qh i q1 o8 xp4 x5 x12 o35 o36)
  (forall (qp1 q2)
    (implies (and (dsq-ptr-p qp1) (dsq-ptr-p q2)) (implies (and (and (and (and (and (and (equal (dsq-data qp1) (dsq-data q2)) (equal (len (dsq-data q2)) (len (dsq-data o36)))) (equal (dsq-offset qp1) (dsq-offset o36))) (equal (dsq-min qp1) (dsq-min o36))) (equal (dsq-max qp1) (dsq-max o36))) (equal (dsq-writable qp1) (dsq-writable o36))) (equal (dsq-zone qp1) (dsq-zone o36))) (implies (and (and (and (and (and (and (equal (dsq-data qp1) (dsq-data q2)) (equal (len (dsq-data q2)) (len (dsq-data o36)))) (equal (dsq-offset qp1) (dsq-offset o36))) (equal (dsq-min qp1) (dsq-min o36))) (equal (dsq-max qp1) (dsq-max o36))) (equal (dsq-writable qp1) (dsq-writable o36))) (equal (dsq-zone qp1) (dsq-zone o36))) (implies (and (and (and (and (and (equal (len (dsq-data q2)) (len (dsq-data q1))) (equal (dsq-offset q2) (dsq-offset q1))) (equal (dsq-min q2) (dsq-min q1))) (equal (dsq-max q2) (dsq-max q1))) (equal (dsq-writable q2) (dsq-writable q1))) (equal (dsq-zone q2) (dsq-zone q1))) (implies (dsq-map-equal-p (dsq-map-base qp1) (dsq-map-update (dsq-map-base o36) (dsq-offset qp1) o35)) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (< (dsq-sint32 o8) (dsq-sint32 i)) (and (<= 0 (dsq-sint32 o8)) (<= (dsq-sint32 o8) (- (dsq-sint32 sx) (dsq-sint32 sy))))) (equal (dsq-offset qp1) (+ (dsq-offset q2) (dsq-sint32 o8)))) (equal (dsq-offset xp4) (- (+ (+ (dsq-offset x5) (dsq-sint32 sy)) (dsq-sint32 o8)) 2))) (equal (len (dsq-data qp1)) (len (dsq-data q2)))) (equal (dsq-min qp1) (dsq-min q2))) (equal (dsq-max qp1) (dsq-max q2))) (equal (len (dsq-data xp4)) (len (dsq-data x5)))) (equal (dsq-min xp4) (dsq-min x5))) (equal (dsq-max xp4) (dsq-max x5))) (dsq-map-equal-p (dsq-map-base qp1) (dsq-map-base q2))) (dsq-map-equal-p (dsq-map-base xp4) (dsq-map-base x5))) (and (equal (dsq-writable qp1) t) (equal (dsq-writable xp4) t))) (equal (dsq-value x (dsq-sint32 sx)) (+ (+ (* (* (+ (dsq-value qp1 (- (- (dsq-sint32 sx) (dsq-sint32 sy)) (dsq-sint32 o8))) (* qh (dsq-ipow (+ 18446744073709551615 1) (- (- (dsq-sint32 sx) (dsq-sint32 sy)) (dsq-sint32 o8))))) vy) (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 o8))) (dsq-value x5 (- (+ (dsq-sint32 sy) (dsq-sint32 o8)) 1))) (* (dsq-ipow (+ 18446744073709551615 1) (- (+ (dsq-sint32 sy) (dsq-sint32 o8)) 1)) x12)))) (< (+ (dsq-value-sub (dsq-map-base x5) (+ (dsq-offset xp4) (dsq-sint32 mdn)) (- (+ (+ (dsq-offset xp4) (dsq-sint32 mdn)) (dsq-sint32 sy)) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) x12)) vy)) (<= (+ (dsq-map-get (dsq-map-base x5) (dsq-offset xp4)) (* (+ 18446744073709551615 1) x12)) (+ dl (* (+ 18446744073709551615 1) dh)))))))))))

(defun-sk dsq-q20-p (sy sx x dh dl mdn vy qh i qp q1 o8 xp4 x5 x12 o35)
  (forall (o36)
    (implies (dsq-ptr-p o36) (implies (and (and (and (and (and (and (and (equal (dsq-offset o36) (+ (dsq-offset qp) (- 1))) (equal (len (dsq-data o36)) (len (dsq-data qp)))) (dsq-map-equal-p (dsq-map-base o36) (dsq-map-base qp))) (equal (dsq-data o36) (dsq-data qp))) (equal (dsq-min o36) (dsq-min qp))) (equal (dsq-max o36) (dsq-max qp))) (equal (dsq-zone o36) (dsq-zone qp))) (equal (dsq-writable o36) (dsq-writable qp))) (let ((o37 (- (- (+ (dsq-offset o36) (dsq-sint32 sx)) (dsq-sint32 sy)) (dsq-sint32 o8)))) (let ((o38 (+ (dsq-offset o36) 1))) (let ((o39 (dsq-offset o36))) (let ((o40 (dsq-map-base q1))) (and (and (<= o38 o37) (or (< o39 o38) (<= o37 o39))) (implies (equal (dsq-value-sub o40 o38 o37) (dsq-value-sub (dsq-map-update o40 o39 o35) o38 o37)) (and (and (and (<= (dsq-min o36) (dsq-offset o36)) (< (dsq-offset o36) (dsq-max o36))) (equal (dsq-writable o36) t)) (dsq-q19-p sy sx x dh dl mdn vy qh i q1 o8 xp4 x5 x12 o35 o36))))))))))))

(defun-sk dsq-q21-p (sy sx x dh dl mdn vy qh i qp q1 o8 qu xp4 x5 x12)
  (forall (o35)
    (implies (dsq-bv64-p o35) (implies (equal o35 (- qu 1)) (and (and (<= (dsq-min qp) (+ (dsq-offset qp) (- 1))) (<= (+ (dsq-offset qp) (- 1)) (dsq-max qp))) (dsq-q20-p sy sx x dh dl mdn vy qh i qp q1 o8 xp4 x5 x12 o35))))))

(defun-sk dsq-q22-p (sy sx x dh dl mdn vy qh i qp q1 o8 qu o19 xd3 xd4 xp4 x5)
  (forall (x12)
    (implies (dsq-bv64-p x12) (implies (equal (+ (dsq-value xd4 (- (dsq-sint32 sy) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) x12)) (- (+ (+ (dsq-value xd3 (- (dsq-sint32 sy) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) o19)) vy) (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 sy)))) (and (dsq-uint64-in-bounds-p (- qu 1)) (dsq-q21-p sy sx x dh dl mdn vy qh i qp q1 o8 qu xp4 x5 x12))))))

(defun-sk dsq-q23-p (sy sx x y dh dl mdn vy qh i qp q1 o8 qu o19 xd3 x4 o34 xd4 xp4 x5)
  (forall (c)
    (implies (dsq-bv64-p c) (implies (and (and (and (<= 0 c) (<= c 1)) (equal (+ (dsq-value xd4 (dsq-sint32 o34)) (* (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 o34)) c)) (+ (dsq-value xd3 (dsq-sint32 o34)) (dsq-value y (dsq-sint32 o34))))) (dsq-q16-p xd3 o34 xd4)) (and (equal (dsq-value x5 (dsq-sint32 o8)) (dsq-value x4 (dsq-sint32 o8))) (implies (equal (dsq-value x5 (dsq-sint32 o8)) (dsq-value x4 (dsq-sint32 o8))) (and (and (not (equal (+ 18446744073709551615 1) 0)) (dsq-q18-p sy dh vy o19 xd3 xd4 c)) (dsq-q22-p sy sx x dh dl mdn vy qh i qp q1 o8 qu o19 xd3 xd4 xp4 x5))))))))

(defun-sk dsq-q24-p (sy sx x y dh dl mdn vy qh i qp q1 o8 qu o19 xd3 xp3 x4 o34)
  (forall (xd4 xp4 x5)
    (implies (and (dsq-ptr-p xd4) (dsq-ptr-p xp4) (dsq-ptr-p x5)) (implies (and (and (and (and (and (and (equal (dsq-data xd4) (dsq-data x5)) (equal (len (dsq-data x5)) (len (dsq-data xd3)))) (equal (dsq-offset xd4) (dsq-offset xd3))) (equal (dsq-min xd4) (dsq-min xd3))) (equal (dsq-max xd4) (dsq-max xd3))) (equal (dsq-writable xd4) (dsq-writable xd3))) (equal (dsq-zone xd4) (dsq-zone xd3))) (implies (and (and (and (and (and (and (equal (dsq-data xp4) (dsq-data x5)) (equal (len (dsq-data x5)) (len (dsq-data xp3)))) (equal (dsq-offset xp4) (dsq-offset xp3))) (equal (dsq-min xp4) (dsq-min xp3))) (equal (dsq-max xp4) (dsq-max xp3))) (equal (dsq-writable xp4) (dsq-writable xp3))) (equal (dsq-zone xp4) (dsq-zone xp3))) (implies (and (and (and (and (and (equal (len (dsq-data x5)) (len (dsq-data x4))) (equal (dsq-offset x5) (dsq-offset x4))) (equal (dsq-min x5) (dsq-min x4))) (equal (dsq-max x5) (dsq-max x4))) (equal (dsq-writable x5) (dsq-writable x4))) (equal (dsq-zone x5) (dsq-zone x4))) (dsq-q23-p sy sx x y dh dl mdn vy qh i qp q1 o8 qu o19 xd3 x4 o34 xd4 xp4 x5)))))))

(defun-sk dsq-q25-p (sy sx x y dh dl mdn vy qh i qp q1 o8 qu o19 xd3 xp3 x4)
  (forall (o34)
    (implies (dsq-bv32-p o34) (implies (equal (dsq-sint32 o34) (- (dsq-sint32 sy) 1)) (and (and (and (dsq-valid-p xd3 (dsq-sint32 o34)) (dsq-valid-p y (dsq-sint32 o34))) (equal (dsq-writable xd3) t)) (dsq-q24-p sy sx x y dh dl mdn vy qh i qp q1 o8 qu o19 xd3 xp3 x4 o34))))))

(defun-sk dsq-q26-p (sy sx x y dh dl mdn vy qh i qp q1 o8 qu o19 xd3 xp3 x4 o33)
  (forall (xc1)
    (implies (dsq-bv64-list-p xc1) (implies (and (equal (len xc1) (len o33)) (dsq-q15-p o33 xc1)) (and (dsq-int32-in-bounds-p (- (dsq-sint32 sy) 1)) (dsq-q25-p sy sx x y dh dl mdn vy qh i qp q1 o8 qu o19 xd3 xp3 x4))))))

(defun-sk dsq-q27-p (sy sx x dh dl mdn vy qh i q1 o8 qu o19 xp3 x4 o33)
  (forall (qp1 q2)
    (implies (and (dsq-ptr-p qp1) (dsq-ptr-p q2)) (implies (and (and (and (and (and (and (equal (dsq-data qp1) (dsq-data q2)) (equal (len (dsq-data q2)) (len (dsq-data o33)))) (equal (dsq-offset qp1) (dsq-offset o33))) (equal (dsq-min qp1) (dsq-min o33))) (equal (dsq-max qp1) (dsq-max o33))) (equal (dsq-writable qp1) (dsq-writable o33))) (equal (dsq-zone qp1) (dsq-zone o33))) (implies (and (and (and (and (and (and (equal (dsq-data qp1) (dsq-data q2)) (equal (len (dsq-data q2)) (len (dsq-data o33)))) (equal (dsq-offset qp1) (dsq-offset o33))) (equal (dsq-min qp1) (dsq-min o33))) (equal (dsq-max qp1) (dsq-max o33))) (equal (dsq-writable qp1) (dsq-writable o33))) (equal (dsq-zone qp1) (dsq-zone o33))) (implies (and (and (and (and (and (equal (len (dsq-data q2)) (len (dsq-data q1))) (equal (dsq-offset q2) (dsq-offset q1))) (equal (dsq-min q2) (dsq-min q1))) (equal (dsq-max q2) (dsq-max q1))) (equal (dsq-writable q2) (dsq-writable q1))) (equal (dsq-zone q2) (dsq-zone q1))) (implies (dsq-map-equal-p (dsq-map-base qp1) (dsq-map-update (dsq-map-base o33) (dsq-offset qp1) qu)) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (< (dsq-sint32 o8) (dsq-sint32 i)) (and (<= 0 (dsq-sint32 o8)) (<= (dsq-sint32 o8) (- (dsq-sint32 sx) (dsq-sint32 sy))))) (equal (dsq-offset qp1) (+ (dsq-offset q2) (dsq-sint32 o8)))) (equal (dsq-offset xp3) (- (+ (+ (dsq-offset x4) (dsq-sint32 sy)) (dsq-sint32 o8)) 2))) (equal (len (dsq-data qp1)) (len (dsq-data q2)))) (equal (dsq-min qp1) (dsq-min q2))) (equal (dsq-max qp1) (dsq-max q2))) (equal (len (dsq-data xp3)) (len (dsq-data x4)))) (equal (dsq-min xp3) (dsq-min x4))) (equal (dsq-max xp3) (dsq-max x4))) (dsq-map-equal-p (dsq-map-base qp1) (dsq-map-base q2))) (dsq-map-equal-p (dsq-map-base xp3) (dsq-map-base x4))) (and (equal (dsq-writable qp1) t) (equal (dsq-writable xp3) t))) (equal (dsq-value x (dsq-sint32 sx)) (+ (+ (* (* (+ (dsq-value qp1 (- (- (dsq-sint32 sx) (dsq-sint32 sy)) (dsq-sint32 o8))) (* qh (dsq-ipow (+ 18446744073709551615 1) (- (- (dsq-sint32 sx) (dsq-sint32 sy)) (dsq-sint32 o8))))) vy) (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 o8))) (dsq-value x4 (- (+ (dsq-sint32 sy) (dsq-sint32 o8)) 1))) (* (dsq-ipow (+ 18446744073709551615 1) (- (+ (dsq-sint32 sy) (dsq-sint32 o8)) 1)) o19)))) (< (+ (dsq-value-sub (dsq-map-base x4) (+ (dsq-offset xp3) (dsq-sint32 mdn)) (- (+ (+ (dsq-offset xp3) (dsq-sint32 mdn)) (dsq-sint32 sy)) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) o19)) vy)) (<= (+ (dsq-map-get (dsq-map-base x4) (dsq-offset xp3)) (* (+ 18446744073709551615 1) o19)) (+ dl (* (+ 18446744073709551615 1) dh)))))))))))

(defun-sk dsq-q28-p (sy sx x dh dl mdn vy qh i qp q1 o8 qu o19 xp3 x4)
  (forall (o33)
    (implies (dsq-ptr-p o33) (implies (and (and (and (and (and (and (and (equal (dsq-offset o33) (+ (dsq-offset qp) (- 1))) (equal (len (dsq-data o33)) (len (dsq-data qp)))) (dsq-map-equal-p (dsq-map-base o33) (dsq-map-base qp))) (equal (dsq-data o33) (dsq-data qp))) (equal (dsq-min o33) (dsq-min qp))) (equal (dsq-max o33) (dsq-max qp))) (equal (dsq-zone o33) (dsq-zone qp))) (equal (dsq-writable o33) (dsq-writable qp))) (let ((o34 (- (- (+ (dsq-offset o33) (dsq-sint32 sx)) (dsq-sint32 sy)) (dsq-sint32 o8)))) (let ((o35 (+ (dsq-offset o33) 1))) (let ((o36 (dsq-offset o33))) (let ((o37 (dsq-map-base q1))) (and (and (<= o35 o34) (or (< o36 o35) (<= o34 o36))) (implies (equal (dsq-value-sub o37 o35 o34) (dsq-value-sub (dsq-map-update o37 o36 qu) o35 o34)) (and (and (and (<= (dsq-min o33) (dsq-offset o33)) (< (dsq-offset o33) (dsq-max o33))) (equal (dsq-writable o33) t)) (dsq-q27-p sy sx x dh dl mdn vy qh i q1 o8 qu o19 xp3 x4 o33))))))))))))

(defun-sk dsq-q29-p (sy sx x y dh dl mdn vy qh i qp q1 o8 qu cy2 o19 xd3 xp3 x4)
  (forall (o32)
    (implies (booleanp o32) (implies (and (implies (equal cy2 0) (equal o32 t)) (implies (equal o32 t) (equal cy2 0))) (if (equal (not o32) t) (and (< 0 qu) (implies (< 0 qu) (and (<= (- (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 sy)) vy) (+ (dsq-value xd3 (- (dsq-sint32 sy) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) o19))) (implies (<= (- (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 sy)) vy) (+ (dsq-value xd3 (- (dsq-sint32 sy) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) o19))) (let ((o33 (dsq-data x4))) (dsq-q26-p sy sx x y dh dl mdn vy qh i qp q1 o8 qu o19 xd3 xp3 x4 o33)))))) (and (and (<= (dsq-min qp) (+ (dsq-offset qp) (- 1))) (<= (+ (dsq-offset qp) (- 1)) (dsq-max qp))) (dsq-q28-p sy sx x dh dl mdn vy qh i qp q1 o8 qu o19 xp3 x4)))))))

(defun-sk dsq-q30-p (sy sx x y dh dl mdn vy qh x11 i qp q1 o8 xd1 qu xd2 xp2 x3 o18 cy2 o19)
  (forall (xd3 xp3 x4)
    (implies (and (dsq-ptr-p xd3) (dsq-ptr-p xp3) (dsq-ptr-p x4)) (implies (and (and (and (and (and (and (equal (dsq-data xp3) (dsq-data x4)) (equal (len (dsq-data x4)) (len (dsq-data xp2)))) (equal (dsq-offset xp3) (dsq-offset xp2))) (equal (dsq-min xp3) (dsq-min xp2))) (equal (dsq-max xp3) (dsq-max xp2))) (equal (dsq-writable xp3) (dsq-writable xp2))) (equal (dsq-zone xp3) (dsq-zone xp2))) (implies (and (and (and (and (and (and (equal (dsq-data xd3) (dsq-data x4)) (equal (len (dsq-data x4)) (len (dsq-data xd2)))) (equal (dsq-offset xd3) (dsq-offset xd2))) (equal (dsq-min xd3) (dsq-min xd2))) (equal (dsq-max xd3) (dsq-max xd2))) (equal (dsq-writable xd3) (dsq-writable xd2))) (equal (dsq-zone xd3) (dsq-zone xd2))) (implies (and (and (and (and (and (and (equal (dsq-data xp3) (dsq-data x4)) (equal (len (dsq-data x4)) (len (dsq-data xp2)))) (equal (dsq-offset xp3) (dsq-offset xp2))) (equal (dsq-min xp3) (dsq-min xp2))) (equal (dsq-max xp3) (dsq-max xp2))) (equal (dsq-writable xp3) (dsq-writable xp2))) (equal (dsq-zone xp3) (dsq-zone xp2))) (implies (and (and (and (and (and (equal (len (dsq-data x4)) (len (dsq-data x3))) (equal (dsq-offset x4) (dsq-offset x3))) (equal (dsq-min x4) (dsq-min x3))) (equal (dsq-max x4) (dsq-max x3))) (equal (dsq-writable x4) (dsq-writable x3))) (equal (dsq-zone x4) (dsq-zone x3))) (implies (dsq-map-equal-p (dsq-map-base xp3) (dsq-map-update (dsq-map-base xp2) (dsq-offset xp3) o18)) (and (equal (- (+ (dsq-value xd3 (- (dsq-sint32 sy) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) o19)) (* (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 sy)) cy2)) (- (+ (dsq-value xd1 (dsq-sint32 sy)) (* (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 sy)) x11)) (* qu vy))) (implies (equal (- (+ (dsq-value xd3 (- (dsq-sint32 sy) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) o19)) (* (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 sy)) cy2)) (- (+ (dsq-value xd1 (dsq-sint32 sy)) (* (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 sy)) x11)) (* qu vy))) (dsq-q29-p sy sx x y dh dl mdn vy qh i qp q1 o8 qu cy2 o19 xd3 xp3 x4)))))))))))

(defun-sk dsq-q31-p (sy sx x y dh dl mdn vy qh x11 i qp q1 o8 xd1 qu rh xd2 xp2 x3 cy1 o18 cy2)
  (forall (o19)
    (implies (dsq-bv64-p o19) (implies (equal o19 (mod (- rh cy1) (+ 18446744073709551615 1))) (let ((o20 (- (+ (dsq-offset xd2) (dsq-sint32 sy)) 1))) (let ((o21 (dsq-offset xd2))) (let ((o22 (dsq-offset xp2))) (let ((o23 (dsq-map-base x3))) (and (and (<= o21 o22) (< o22 o20)) (implies (equal (dsq-value-sub (dsq-map-update o23 o22 o18) o21 o20) (+ (dsq-value-sub o23 o21 o20) (* (dsq-ipow (+ 18446744073709551615 1) (- o22 o21)) (- o18 (dsq-map-get o23 o22))))) (let ((o24 (+ (dsq-offset x3) (dsq-sint32 o8)))) (let ((o25 (dsq-offset x3))) (let ((o26 (dsq-offset xp2))) (let ((o27 (dsq-map-base x3))) (and (and (<= o25 o24) (or (< o26 o25) (<= o24 o26))) (implies (equal (dsq-value-sub o27 o25 o24) (dsq-value-sub (dsq-map-update o27 o26 o18) o25 o24)) (let ((o28 (- (+ (dsq-offset xd2) (dsq-sint32 sy)) 2))) (let ((o29 (dsq-offset xd2))) (let ((o30 (dsq-offset xp2))) (let ((o31 (dsq-map-base x3))) (and (and (<= o29 o28) (or (< o30 o29) (<= o28 o30))) (implies (equal (dsq-value-sub o31 o29 o28) (dsq-value-sub (dsq-map-update o31 o30 o18) o29 o28)) (and (and (and (<= (dsq-min xp2) (dsq-offset xp2)) (< (dsq-offset xp2) (dsq-max xp2))) (equal (dsq-writable xp2) t)) (dsq-q30-p sy sx x y dh dl mdn vy qh x11 i qp q1 o8 xd1 qu xd2 xp2 x3 o18 cy2 o19))))))))))))))))))))))))

(defun-sk dsq-q32-p (sy sx x y dh dl mdn vy qh x11 i qp q1 o8 xd1 qu rh xd2 xp2 x3 cy1 o18)
  (forall (cy2)
    (implies (dsq-bv64-p cy2) (implies (if (< rh cy1) (equal cy2 1) (equal cy2 0)) (dsq-q31-p sy sx x y dh dl mdn vy qh x11 i qp q1 o8 xd1 qu rh xd2 xp2 x3 cy1 o18 cy2)))))

(defun-sk dsq-q33-p (sy sx x y dh dl mdn vy qh x11 i qp q1 o8 xd1 qu rl rh xd2 xp2 x3 cy cy1)
  (forall (o18)
    (implies (dsq-bv64-p o18) (implies (equal o18 (mod (- rl cy) (+ 18446744073709551615 1))) (dsq-q32-p sy sx x y dh dl mdn vy qh x11 i qp q1 o8 xd1 qu rh xd2 xp2 x3 cy1 o18)))))

(defun-sk dsq-q34-p (sy sx x y dh dl mdn vy qh x11 i qp q1 o8 xd1 qu rl rh xd2 xp2 x3 cy)
  (forall (cy1)
    (implies (dsq-bv64-p cy1) (implies (if (< rl cy) (equal cy1 1) (equal cy1 0)) (dsq-q33-p sy sx x y dh dl mdn vy qh x11 i qp q1 o8 xd1 qu rl rh xd2 xp2 x3 cy cy1)))))

(defun-sk dsq-q35-p (sy sx x y dh dl mdn vy qh x11 i qp x2 q1 o8 xd1 qu rl rh o17 xd2 xp2 x3)
  (forall (cy)
    (implies (dsq-bv64-p cy) (implies (and (equal (- (dsq-value xd2 (dsq-sint32 o17)) (* (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 o17)) cy)) (- (dsq-value xd1 (dsq-sint32 o17)) (* (dsq-value y (dsq-sint32 o17)) qu))) (dsq-q14-p xd1 o17 xd2)) (and (equal (dsq-value x3 (dsq-sint32 o8)) (dsq-value x2 (dsq-sint32 o8))) (implies (equal (dsq-value x3 (dsq-sint32 o8)) (dsq-value x2 (dsq-sint32 o8))) (dsq-q34-p sy sx x y dh dl mdn vy qh x11 i qp q1 o8 xd1 qu rl rh xd2 xp2 x3 cy)))))))

(defun-sk dsq-q36-p (sy sx x y dh dl mdn vy qh x11 i qp x2 q1 o8 o9 xd1 qu rl rh o17)
  (forall (xd2 xp2 x3)
    (implies (and (dsq-ptr-p xd2) (dsq-ptr-p xp2) (dsq-ptr-p x3)) (implies (and (and (and (and (and (and (equal (dsq-data xd2) (dsq-data x3)) (equal (len (dsq-data x3)) (len (dsq-data xd1)))) (equal (dsq-offset xd2) (dsq-offset xd1))) (equal (dsq-min xd2) (dsq-min xd1))) (equal (dsq-max xd2) (dsq-max xd1))) (equal (dsq-writable xd2) (dsq-writable xd1))) (equal (dsq-zone xd2) (dsq-zone xd1))) (implies (and (and (and (and (and (and (equal (dsq-data xp2) (dsq-data x3)) (equal (len (dsq-data x3)) (len (dsq-data o9)))) (equal (dsq-offset xp2) (dsq-offset o9))) (equal (dsq-min xp2) (dsq-min o9))) (equal (dsq-max xp2) (dsq-max o9))) (equal (dsq-writable xp2) (dsq-writable o9))) (equal (dsq-zone xp2) (dsq-zone o9))) (implies (and (and (and (and (and (equal (len (dsq-data x3)) (len (dsq-data x2))) (equal (dsq-offset x3) (dsq-offset x2))) (equal (dsq-min x3) (dsq-min x2))) (equal (dsq-max x3) (dsq-max x2))) (equal (dsq-writable x3) (dsq-writable x2))) (equal (dsq-zone x3) (dsq-zone x2))) (dsq-q35-p sy sx x y dh dl mdn vy qh x11 i qp x2 q1 o8 xd1 qu rl rh o17 xd2 xp2 x3)))))))

(defun-sk dsq-q37-p (sy sx x y dh dl mdn vy qh x11 i qp x2 q1 o8 o9 xd1 qu rl rh)
  (forall (o17)
    (implies (dsq-bv32-p o17) (implies (equal (dsq-sint32 o17) (- (dsq-sint32 sy) 2)) (and (and (and (dsq-valid-p y (dsq-sint32 o17)) (dsq-valid-p xd1 (dsq-sint32 o17))) (equal (dsq-writable xd1) t)) (dsq-q36-p sy sx x y dh dl mdn vy qh x11 i qp x2 q1 o8 o9 xd1 qu rl rh o17))))))

(defun-sk dsq-q38-p (sy sx x y dh dl mdn vy qh x11 i qp x2 q1 o8 o9 xd1 qu rl rh o16)
  (forall (xc)
    (implies (dsq-bv64-list-p xc) (implies (and (equal (len xc) (len o16)) (dsq-q13-p o16 xc)) (and (dsq-int32-in-bounds-p (- (dsq-sint32 sy) 2)) (dsq-q37-p sy sx x y dh dl mdn vy qh x11 i qp x2 q1 o8 o9 xd1 qu rl rh))))))

(defun-sk dsq-q39-p (sy sx x y dh dl mdn vy qh x11 i qp x2 q1 o8 o9 xd1 xp0 xp11)
  (forall (qu rl rh)
    (implies (and (dsq-bv64-p qu) (dsq-bv64-p rl) (dsq-bv64-p rh)) (implies (and (and (equal (+ (+ (+ (* qu dl) (* (* (+ 18446744073709551615 1) qu) dh)) rl) (* (+ 18446744073709551615 1) rh)) (+ (+ xp0 (* (+ 18446744073709551615 1) xp11)) (* (* (+ 18446744073709551615 1) (+ 18446744073709551615 1)) x11))) (<= 0 (+ rl (* (+ 18446744073709551615 1) rh)))) (< (+ rl (* (+ 18446744073709551615 1) rh)) (+ dl (* (+ 18446744073709551615 1) dh)))) (let ((o12 (- (+ (+ (dsq-offset x2) (dsq-sint32 sy)) (dsq-sint32 i)) 1))) (let ((o13 (dsq-offset xd1))) (let ((o14 (dsq-offset x2))) (let ((o15 (dsq-map-base x2))) (and (and (<= o14 o13) (<= o13 o12)) (implies (equal (dsq-value-sub o15 o14 o12) (+ (dsq-value-sub o15 o14 o13) (* (dsq-value-sub o15 o13 o12) (dsq-ipow (+ 18446744073709551615 1) (- o13 o14))))) (let ((o16 (dsq-data x2))) (dsq-q38-p sy sx x y dh dl mdn vy qh x11 i qp x2 q1 o8 o9 xd1 qu rl rh o16))))))))))))

(defun-sk dsq-q40-p (sy sx x y dh dl v mdn vy qh x11 i qp x2 q1 o8 o9 xd1 nx0 o10)
  (forall (o11)
    (implies (booleanp o11) (implies (if (equal o10 t) (and (implies (equal nx0 dl) (equal o11 t)) (implies (equal o11 t) (equal nx0 dl))) (equal o11 nil)) (if (equal o11 t) (and (< (+ (+ (dsq-value-sub (dsq-map-base xd1) (+ (dsq-offset xd1) 1) (- (+ (dsq-offset xd1) (dsq-sint32 sy)) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 2)) dl)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) dh)) vy) (implies (< (+ (+ (dsq-value-sub (dsq-map-base xd1) (+ (dsq-offset xd1) 1) (- (+ (dsq-offset xd1) (dsq-sint32 sy)) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 2)) dl)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) dh)) vy) (let ((o12 (dsq-data x2))) (dsq-q12-p sy sx x y dh dl mdn vy qh i qp x2 q1 o8 o9 xd1 o12)))) (let ((vlx (dsq-value xd1 (- (dsq-sint32 sy) 2)))) (and (and (<= (dsq-min o9) (dsq-offset o9)) (< (dsq-offset o9) (dsq-max o9))) (let ((xp0 (dsq-map-get (dsq-map-base o9) (dsq-offset o9)))) (and (and (<= (dsq-min o9) (+ (dsq-offset o9) 1)) (< (+ (dsq-offset o9) 1) (dsq-max o9))) (let ((xp11 (dsq-map-get (dsq-map-base o9) (+ (dsq-offset o9) 1)))) (and (equal (dsq-value xd1 (dsq-sint32 sy)) (+ vlx (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 2)) (+ xp0 (* (+ 18446744073709551615 1) xp11))))) (implies (equal (dsq-value xd1 (dsq-sint32 sy)) (+ vlx (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 2)) (+ xp0 (* (+ 18446744073709551615 1) xp11))))) (and (and (and (<= (floor (+ 18446744073709551615 1) 2) dh) (dsq-reciprocal-3by2-p v dh dl)) (< (+ xp11 (* (+ 18446744073709551615 1) x11)) (+ dl (* (+ 18446744073709551615 1) dh)))) (dsq-q39-p sy sx x y dh dl mdn vy qh x11 i qp x2 q1 o8 o9 xd1 xp0 xp11))))))))))))))

(defun-sk dsq-q41-p (sy sx x y dh dl v mdn vy qh x11 i qp x2 q1 o8 o9 xd1 nx0)
  (forall (o10)
    (implies (booleanp o10) (implies (and (implies (equal x11 dh) (equal o10 t)) (implies (equal o10 t) (equal x11 dh))) (dsq-q40-p sy sx x y dh dl v mdn vy qh x11 i qp x2 q1 o8 o9 xd1 nx0 o10)))))

(defun-sk dsq-q42-p (sy sx x y dh dl v mdn vy qh x11 i qp x2 q1 o8 o9)
  (forall (xd1)
    (implies (dsq-ptr-p xd1) (implies (and (and (and (and (and (and (and (equal (dsq-offset xd1) (+ (dsq-offset o9) (dsq-sint32 mdn))) (equal (len (dsq-data xd1)) (len (dsq-data o9)))) (dsq-map-equal-p (dsq-map-base xd1) (dsq-map-base o9))) (equal (dsq-data xd1) (dsq-data o9))) (equal (dsq-min xd1) (dsq-min o9))) (equal (dsq-max xd1) (dsq-max o9))) (equal (dsq-zone xd1) (dsq-zone o9))) (equal (dsq-writable xd1) (dsq-writable o9))) (and (and (<= (dsq-min o9) (+ (dsq-offset o9) 1)) (< (+ (dsq-offset o9) 1) (dsq-max o9))) (let ((nx0 (dsq-map-get (dsq-map-base o9) (+ (dsq-offset o9) 1)))) (dsq-q41-p sy sx x y dh dl v mdn vy qh x11 i qp x2 q1 o8 o9 xd1 nx0)))))))

(defun-sk dsq-q43-p (sy sx x y dh dl v mdn vy qh x11 i qp xp1 x2 q1 o8)
  (forall (o9)
    (implies (dsq-ptr-p o9) (implies (and (and (and (and (and (and (and (equal (dsq-offset o9) (+ (dsq-offset xp1) (- 1))) (equal (len (dsq-data o9)) (len (dsq-data xp1)))) (dsq-map-equal-p (dsq-map-base o9) (dsq-map-base xp1))) (equal (dsq-data o9) (dsq-data xp1))) (equal (dsq-min o9) (dsq-min xp1))) (equal (dsq-max o9) (dsq-max xp1))) (equal (dsq-zone o9) (dsq-zone xp1))) (equal (dsq-writable o9) (dsq-writable xp1))) (and (and (<= (dsq-min o9) (+ (dsq-offset o9) (dsq-sint32 mdn))) (<= (+ (dsq-offset o9) (dsq-sint32 mdn)) (dsq-max o9))) (dsq-q42-p sy sx x y dh dl v mdn vy qh x11 i qp x2 q1 o8 o9))))))

(defun-sk dsq-q44-p (sy sx x y dh dl v mdn vy qh x11 i qp xp1 x2 q1)
  (forall (o8)
    (implies (dsq-bv32-p o8) (implies (equal (dsq-sint32 o8) (- (dsq-sint32 i) 1)) (and (and (<= (dsq-min xp1) (+ (dsq-offset xp1) (- 1))) (<= (+ (dsq-offset xp1) (- 1)) (dsq-max xp1))) (dsq-q43-p sy sx x y dh dl v mdn vy qh x11 i qp xp1 x2 q1 o8))))))

(defun-sk dsq-q45-p (sy sx x y qh x11 xp1 x2 q1)
  (forall (o12 x3)
    (implies (and (dsq-ptr-p o12) (dsq-ptr-p x3)) (implies (and (and (and (and (and (and (equal (dsq-data o12) (dsq-data x3)) (equal (len (dsq-data x3)) (len (dsq-data xp1)))) (equal (dsq-offset o12) (dsq-offset xp1))) (equal (dsq-min o12) (dsq-min xp1))) (equal (dsq-max o12) (dsq-max xp1))) (equal (dsq-writable o12) (dsq-writable xp1))) (equal (dsq-zone o12) (dsq-zone xp1))) (implies (and (and (and (and (and (equal (len (dsq-data x3)) (len (dsq-data x2))) (equal (dsq-offset x3) (dsq-offset x2))) (equal (dsq-min x3) (dsq-min x2))) (equal (dsq-max x3) (dsq-max x2))) (equal (dsq-writable x3) (dsq-writable x2))) (equal (dsq-zone x3) (dsq-zone x2))) (implies (and (dsq-map-equal-p (dsq-map-base o12) (dsq-map-update (dsq-map-base xp1) (+ (dsq-offset o12) 1) x11)) (equal (dsq-map-get (dsq-map-base o12) (+ (dsq-offset o12) 1)) x11)) (and (and (and (equal (dsq-value x (dsq-sint32 sx)) (+ (* (+ (dsq-value q1 (- (dsq-sint32 sx) (dsq-sint32 sy))) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sx) (dsq-sint32 sy))) qh)) (dsq-value y (dsq-sint32 sy))) (dsq-value x3 (dsq-sint32 sy)))) (< (dsq-value x3 (dsq-sint32 sy)) (dsq-value y (dsq-sint32 sy)))) (<= 0 qh)) (<= qh 1))))))))

(defun-sk dsq-q46-p (sy sx x y q dh dl v mdn vy qh x1)
  (forall (x11 i qp xp1 x2 q1)
    (implies (and (dsq-bv64-p x11) (dsq-bv32-p i) (dsq-ptr-p qp) (dsq-ptr-p xp1) (dsq-ptr-p x2) (dsq-ptr-p q1)) (implies (and (and (and (and (and (equal (len (dsq-data x2)) (len (dsq-data x1))) (equal (dsq-offset x2) (dsq-offset x1))) (equal (dsq-min x2) (dsq-min x1))) (equal (dsq-max x2) (dsq-max x1))) (equal (dsq-writable x2) (dsq-writable x1))) (equal (dsq-zone x2) (dsq-zone x1))) (implies (and (and (and (and (and (equal (len (dsq-data q1)) (len (dsq-data q))) (equal (dsq-offset q1) (dsq-offset q))) (equal (dsq-min q1) (dsq-min q))) (equal (dsq-max q1) (dsq-max q))) (equal (dsq-writable q1) (dsq-writable q))) (equal (dsq-zone q1) (dsq-zone q))) (implies (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= 0 (dsq-sint32 i)) (<= (dsq-sint32 i) (- (dsq-sint32 sx) (dsq-sint32 sy)))) (equal (dsq-offset qp) (+ (dsq-offset q1) (dsq-sint32 i)))) (equal (dsq-offset xp1) (- (+ (+ (dsq-offset x2) (dsq-sint32 sy)) (dsq-sint32 i)) 2))) (equal (len (dsq-data qp)) (len (dsq-data q1)))) (equal (dsq-min qp) (dsq-min q1))) (equal (dsq-max qp) (dsq-max q1))) (equal (len (dsq-data xp1)) (len (dsq-data x2)))) (equal (dsq-min xp1) (dsq-min x2))) (equal (dsq-max xp1) (dsq-max x2))) (dsq-map-equal-p (dsq-map-base qp) (dsq-map-base q1))) (dsq-map-equal-p (dsq-map-base xp1) (dsq-map-base x2))) (and (equal (dsq-writable qp) t) (equal (dsq-writable xp1) t))) (equal (dsq-value x (dsq-sint32 sx)) (+ (+ (* (* (+ (dsq-value qp (- (- (dsq-sint32 sx) (dsq-sint32 sy)) (dsq-sint32 i))) (* qh (dsq-ipow (+ 18446744073709551615 1) (- (- (dsq-sint32 sx) (dsq-sint32 sy)) (dsq-sint32 i))))) vy) (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 i))) (dsq-value x2 (- (+ (dsq-sint32 sy) (dsq-sint32 i)) 1))) (* (dsq-ipow (+ 18446744073709551615 1) (- (+ (dsq-sint32 sy) (dsq-sint32 i)) 1)) x11)))) (< (+ (dsq-value-sub (dsq-map-base x2) (+ (dsq-offset xp1) (dsq-sint32 mdn)) (- (+ (+ (dsq-offset xp1) (dsq-sint32 mdn)) (dsq-sint32 sy)) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) x11)) vy)) (<= (+ (dsq-map-get (dsq-map-base x2) (dsq-offset xp1)) (* (+ 18446744073709551615 1) x11)) (+ dl (* (+ 18446744073709551615 1) dh)))) (if (< 0 (dsq-sint32 i)) (and (dsq-int32-in-bounds-p (- (dsq-sint32 i) 1)) (dsq-q44-p sy sx x y dh dl v mdn vy qh x11 i qp xp1 x2 q1)) (let ((o8 (dsq-offset xp1))) (let ((o9 (dsq-offset x2))) (let ((o10 (+ (dsq-offset xp1) 1))) (let ((o11 (dsq-map-base x2))) (and (and (<= o9 o8) (or (< o10 o9) (<= o8 o10))) (implies (equal (dsq-value-sub o11 o9 o8) (dsq-value-sub (dsq-map-update o11 o10 x11) o9 o8)) (and (and (and (<= (dsq-min xp1) (+ (dsq-offset xp1) 1)) (< (+ (dsq-offset xp1) 1) (dsq-max xp1))) (equal (dsq-writable xp1) t)) (dsq-q45-p sy sx x y qh x11 xp1 x2 q1)))))))))))))))

(defun-sk dsq-q47-p (sy sx x y q o2 o4 dh dl v o7 mdn xd vy qh)
  (forall (x1 xp)
    (implies (and (dsq-ptr-p x1) (dsq-ptr-p xp)) (implies (dsq-q5-p sy x y o2 xd qh x1 xp) (and (and (and (and (<= (dsq-min xp) (+ (dsq-offset xp) 1)) (< (+ (dsq-offset xp) 1) (dsq-max xp))) (and (<= (dsq-min xp) (+ (dsq-offset xp) 1)) (< (+ (dsq-offset xp) 1) (dsq-max xp)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= 0 (dsq-sint32 o7)) (<= (dsq-sint32 o7) (- (dsq-sint32 sx) (dsq-sint32 sy)))) (equal (dsq-offset o4) (+ (dsq-offset q) (dsq-sint32 o7)))) (equal (dsq-offset xp) (- (+ (+ (dsq-offset x1) (dsq-sint32 sy)) (dsq-sint32 o7)) 2))) (equal (len (dsq-data o4)) (len (dsq-data q)))) (equal (dsq-min o4) (dsq-min q))) (equal (dsq-max o4) (dsq-max q))) (equal (len (dsq-data xp)) (len (dsq-data x1)))) (equal (dsq-min xp) (dsq-min x1))) (equal (dsq-max xp) (dsq-max x1))) (dsq-map-equal-p (dsq-map-base o4) (dsq-map-base q))) (dsq-map-equal-p (dsq-map-base xp) (dsq-map-base x1))) (and (equal (dsq-writable o4) t) (equal (dsq-writable xp) t))) (equal (dsq-value x (dsq-sint32 sx)) (+ (+ (* (* (+ (dsq-value o4 (- (- (dsq-sint32 sx) (dsq-sint32 sy)) (dsq-sint32 o7))) (* qh (dsq-ipow (+ 18446744073709551615 1) (- (- (dsq-sint32 sx) (dsq-sint32 sy)) (dsq-sint32 o7))))) vy) (dsq-ipow (+ 18446744073709551615 1) (dsq-sint32 o7))) (dsq-value x1 (- (+ (dsq-sint32 sy) (dsq-sint32 o7)) 1))) (* (dsq-ipow (+ 18446744073709551615 1) (- (+ (dsq-sint32 sy) (dsq-sint32 o7)) 1)) (dsq-map-get (dsq-map-base xp) (+ (dsq-offset xp) 1)))))) (< (+ (dsq-value-sub (dsq-map-base x1) (+ (dsq-offset xp) (dsq-sint32 mdn)) (- (+ (+ (dsq-offset xp) (dsq-sint32 mdn)) (dsq-sint32 sy)) 1)) (* (dsq-ipow (+ 18446744073709551615 1) (- (dsq-sint32 sy) 1)) (dsq-map-get (dsq-map-base xp) (+ (dsq-offset xp) 1)))) vy)) (<= (+ (dsq-map-get (dsq-map-base x1) (dsq-offset xp)) (* (+ 18446744073709551615 1) (dsq-map-get (dsq-map-base xp) (+ (dsq-offset xp) 1)))) (+ dl (* (+ 18446744073709551615 1) dh))))) (dsq-q46-p sy sx x y q dh dl v mdn vy qh x1))))))

(defun-sk dsq-q48-p (sy sx x y q o2 o4 dh dl v o7 mdn xd vy r)
  (forall (qh)
    (implies (dsq-bv64-p qh) (implies (if (<= 0 (dsq-sint32 r)) (equal qh 1) (equal qh 0)) (and (dsq-q1-p sy y xd qh) (dsq-q47-p sy sx x y q o2 o4 dh dl v o7 mdn xd vy qh))))))

(defun-sk dsq-q49-p (sy sx x y q o2 o4 dh dl v o7 mdn xd vy)
  (forall (r)
    (implies (dsq-bv32-p r) (implies (equal (dsq-sint32 r) (dsq-compare-int (dsq-value xd (dsq-sint32 sy)) (dsq-value y (dsq-sint32 sy)))) (dsq-q48-p sy sx x y q o2 o4 dh dl v o7 mdn xd vy r)))))

(defun-sk dsq-q50-p (sy sx x y q o2 o4 dh dl v o7 mdn)
  (forall (xd)
    (implies (dsq-ptr-p xd) (implies (and (and (and (and (and (and (and (equal (dsq-offset xd) (+ (dsq-offset o2) (dsq-sint32 mdn))) (equal (len (dsq-data xd)) (len (dsq-data o2)))) (dsq-map-equal-p (dsq-map-base xd) (dsq-map-base o2))) (equal (dsq-data xd) (dsq-data o2))) (equal (dsq-min xd) (dsq-min o2))) (equal (dsq-max xd) (dsq-max o2))) (equal (dsq-zone xd) (dsq-zone o2))) (equal (dsq-writable xd) (dsq-writable o2))) (let ((vy (dsq-value y (dsq-sint32 sy)))) (and (and (dsq-valid-p xd (dsq-sint32 sy)) (dsq-valid-p y (dsq-sint32 sy))) (dsq-q49-p sy sx x y q o2 o4 dh dl v o7 mdn xd vy)))))))

(defun-sk dsq-q51-p (sy sx x y q o2 o4 dh dl v o7)
  (forall (mdn)
    (implies (dsq-bv32-p mdn) (implies (equal (dsq-sint32 mdn) (- 2 (dsq-sint32 sy))) (and (and (<= (dsq-min o2) (+ (dsq-offset o2) (dsq-sint32 mdn))) (<= (+ (dsq-offset o2) (dsq-sint32 mdn)) (dsq-max o2))) (dsq-q50-p sy sx x y q o2 o4 dh dl v o7 mdn))))))

(defun-sk dsq-q52-p (sy sx x y q o2 o4 dh dl v)
  (forall (o7)
    (implies (dsq-bv32-p o7) (implies (equal (dsq-sint32 o7) (- (dsq-sint32 sx) (dsq-sint32 sy))) (and (dsq-int32-in-bounds-p (- 2 (dsq-sint32 sy))) (dsq-q51-p sy sx x y q o2 o4 dh dl v o7))))))

(defun-sk dsq-q53-p (sy sx x y q o2 o4 dh dl)
  (forall (v)
    (implies (dsq-bv64-p v) (implies (dsq-reciprocal-3by2-p v dh dl) (and (dsq-int32-in-bounds-p (- (dsq-sint32 sx) (dsq-sint32 sy))) (dsq-q52-p sy sx x y q o2 o4 dh dl v))))))

(defun-sk dsq-q54-p (sy sx x y q o2 o4 dh)
  (forall (o6)
    (implies (dsq-bv32-p o6) (implies (equal (dsq-sint32 o6) (- (dsq-sint32 sy) 2)) (and (and (<= (dsq-min y) (+ (dsq-offset y) (dsq-sint32 o6))) (< (+ (dsq-offset y) (dsq-sint32 o6)) (dsq-max y))) (let ((dl (dsq-map-get (dsq-map-base y) (+ (dsq-offset y) (dsq-sint32 o6))))) (and (<= (floor (+ 18446744073709551615 1) 2) dh) (dsq-q53-p sy sx x y q o2 o4 dh dl))))))))

(defun-sk dsq-q55-p (sy sx x y q o2 o4)
  (forall (o5)
    (implies (dsq-bv32-p o5) (implies (equal (dsq-sint32 o5) (- (dsq-sint32 sy) 1)) (and (and (<= (dsq-min y) (+ (dsq-offset y) (dsq-sint32 o5))) (< (+ (dsq-offset y) (dsq-sint32 o5)) (dsq-max y))) (let ((dh (dsq-map-get (dsq-map-base y) (+ (dsq-offset y) (dsq-sint32 o5))))) (and (dsq-int32-in-bounds-p (- (dsq-sint32 sy) 2)) (dsq-q54-p sy sx x y q o2 o4 dh))))))))

(defun-sk dsq-q56-p (sy sx x y q o2 o3)
  (forall (o4)
    (implies (dsq-ptr-p o4) (implies (and (and (and (and (and (and (and (equal (dsq-offset o4) (+ (dsq-offset q) (dsq-sint32 o3))) (equal (len (dsq-data o4)) (len (dsq-data q)))) (dsq-map-equal-p (dsq-map-base o4) (dsq-map-base q))) (equal (dsq-data o4) (dsq-data q))) (equal (dsq-min o4) (dsq-min q))) (equal (dsq-max o4) (dsq-max q))) (equal (dsq-zone o4) (dsq-zone q))) (equal (dsq-writable o4) (dsq-writable q))) (and (dsq-int32-in-bounds-p (- (dsq-sint32 sy) 1)) (dsq-q55-p sy sx x y q o2 o4))))))

(defun-sk dsq-q57-p (sy sx x y q o2)
  (forall (o3)
    (implies (dsq-bv32-p o3) (implies (equal (dsq-sint32 o3) (- (dsq-sint32 sx) (dsq-sint32 sy))) (and (and (<= (dsq-min q) (+ (dsq-offset q) (dsq-sint32 o3))) (<= (+ (dsq-offset q) (dsq-sint32 o3)) (dsq-max q))) (dsq-q56-p sy sx x y q o2 o3))))))

(defun-sk dsq-q58-p (sy sx x y q o1)
  (forall (o2)
    (implies (dsq-ptr-p o2) (implies (and (and (and (and (and (and (and (equal (dsq-offset o2) (+ (dsq-offset x) (dsq-sint32 o1))) (equal (len (dsq-data o2)) (len (dsq-data x)))) (dsq-map-equal-p (dsq-map-base o2) (dsq-map-base x))) (equal (dsq-data o2) (dsq-data x))) (equal (dsq-min o2) (dsq-min x))) (equal (dsq-max o2) (dsq-max x))) (equal (dsq-zone o2) (dsq-zone x))) (equal (dsq-writable o2) (dsq-writable x))) (and (dsq-int32-in-bounds-p (- (dsq-sint32 sx) (dsq-sint32 sy))) (dsq-q57-p sy sx x y q o2))))))

(defun-sk dsq-q59-p (sy sx x y q)
  (forall (o1)
    (implies (dsq-bv32-p o1) (implies (equal (dsq-sint32 o1) (- (dsq-sint32 sx) 2)) (and (and (<= (dsq-min x) (+ (dsq-offset x) (dsq-sint32 o1))) (<= (+ (dsq-offset x) (dsq-sint32 o1)) (dsq-max x))) (dsq-q58-p sy sx x y q o1))))))

(defun-sk dsq-statement-p ()
  (forall (sy sx x y q)
    (implies
     (and (dsq-bv32-p sy)
          (dsq-bv32-p sx)
          (dsq-ptr-p x)
          (dsq-ptr-p y)
          (dsq-ptr-p q))
     (implies
      (and
       (<= 3 (dsq-sint32 sy))
       (<= (dsq-sint32 sy) (dsq-sint32 sx))
       (dsq-valid-p x (dsq-sint32 sx))
       (dsq-valid-p y (dsq-sint32 sy))
       (dsq-valid-p q (- (dsq-sint32 sx) (dsq-sint32 sy)))
       (equal (dsq-writable q) t)
       (equal (dsq-writable x) t)
       (dsq-normalized-p y sy))
      (and (dsq-int32-in-bounds-p (- (dsq-sint32 sx) 2)) (dsq-q59-p sy sx x y q))))))

(value-triple :itpeval-statement-checked)
:q
