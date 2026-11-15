;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/div_Div_div_qr_in_placeqtvc: the verification
;; condition for in-place multi-precision quotient/remainder division,
;; including one- and two-limb special cases, normalization, pointer updates,
;; and the final quotient/remainder equations. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defconst *dqip-radix* 18446744073709551616)
(defconst *dqip-bv32-modulus* 4294967296)
(defconst *dqip-bv32-sign* 2147483648)

;; Canonical integers represent fixed-width words bijectively.

(defun dqip-bv64-p (x)
  (and (integerp x) (<= 0 x) (< x *dqip-radix*)))

(defun dqip-bv32-p (x)
  (and (integerp x) (<= 0 x) (< x *dqip-bv32-modulus*)))

(defun dqip-sint32 (x)
  (if (< x *dqip-bv32-sign*)
      x
    (- x *dqip-bv32-modulus*)))

(defun dqip-int32-in-bounds-p (x)
  (and (integerp x)
       (<= (- *dqip-bv32-sign*) x)
       (<= x (- *dqip-bv32-sign* 1))))

(defun dqip-ipow (base exponent)
  (expt base (nfix exponent)))

;; Source pointers and zones are arbitrary inhabited carrier types.  A
;; pointer's finite data length is independent of its total integer-indexed
;; limb map, matching Why3 arrays rather than a clamped ACL2 list.

(defstub dqip-ptr-p (p) t)
(defstub dqip-zone-p (z) t)
(defstub dqip-data-length (p) t)
(defstub dqip-pelts (p i) t)
(defstub dqip-offset (p) t)
(defstub dqip-min (p) t)
(defstub dqip-max (p) t)
(defstub dqip-writable (p) t)
(defstub dqip-zone (p) t)

(defun-sk dqip-pointer-domain-nonempty-p ()
  (exists (p)
    (dqip-ptr-p p)))

(defun-sk dqip-pointer-interface-typed-p ()
  (forall (p i)
    (implies
     (dqip-ptr-p p)
     (and
      (natp (dqip-data-length p))
      (integerp (dqip-offset p))
      (integerp (dqip-min p))
      (integerp (dqip-max p))
      (booleanp (dqip-writable p))
      (dqip-zone-p (dqip-zone p))
      (implies
       (integerp i)
       (dqip-bv64-p (dqip-pelts p i)))))))

(defun dqip-interface-p ()
  (and
   (dqip-pointer-domain-nonempty-p)
   (dqip-pointer-interface-typed-p)))

(defun dqip-valid-p (p size)
  (and (dqip-int32-in-bounds-p size)
       (<= 0 size)
       (<= 0 (dqip-min p))
       (<= (dqip-min p) (dqip-offset p))
       (<= (+ (dqip-offset p) size) (dqip-max p))
       (<= (dqip-max p) (dqip-data-length p))))

(defun dqip-value-from (p index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (dqip-pelts p index)
       (* *dqip-radix*
          (dqip-value-from p (+ index 1) (- count 1))))))

(defun dqip-value (p size)
  (dqip-value-from p (dqip-offset p) (nfix size)))

(defun dqip-normalized-p (p size-word)
  (let ((size (dqip-sint32 size-word)))
    (and (dqip-valid-p p size)
         (<= (floor *dqip-radix* 2)
             (dqip-pelts p
                         (- (+ (dqip-offset p) size) 1))))))

(defun dqip-same-shape-p (new old)
  (and (equal (dqip-data-length new) (dqip-data-length old))
       (equal (dqip-offset new) (dqip-offset old))
       (equal (dqip-min new) (dqip-min old))
       (equal (dqip-max new) (dqip-max old))
       (equal (dqip-writable new) (dqip-writable old))
       (equal (dqip-zone new) (dqip-zone old))))

(defun-sk dqip-map-eq-sub-shift-p (new old size)
  (forall (i)
    (implies
     (and (integerp i) (<= 0 i) (< i size))
     (equal
      (dqip-pelts new (+ (dqip-offset new) i))
      (dqip-pelts old (+ (dqip-offset old) i))))))

(defun-sk dqip-outside-equal-p (new old size)
  (forall (j)
    (implies
     (and
      (integerp j)
      (or (< j (dqip-offset new))
          (<= (+ (dqip-offset new) size) j)))
     (equal (dqip-pelts new j) (dqip-pelts old j)))))

(defun-sk dqip-update-p (new old index value)
  (forall (j)
    (implies
     (integerp j)
     (equal
      (dqip-pelts new j)
      (if (equal j index) value (dqip-pelts old j))))))

(defun dqip-copy-p (new source original-destination size)
  (and (dqip-map-eq-sub-shift-p new source size)
       (dqip-outside-equal-p new original-destination size)))

(defun dqip-bounds-at-p (p index)
  (and (<= (dqip-min p) (+ (dqip-offset p) index))
       (< (+ (dqip-offset p) index) (dqip-max p))))

(defun dqip-final-result-p (x q y remainder sx sy)
  (and
   (equal
    (dqip-value x sx)
    (+ (* (dqip-value q (+ (- sx sy) 1))
          (dqip-value y sy))
       (dqip-value remainder sy)))
   (< (dqip-value remainder sy) (dqip-value y sy))))

;; Final optional zero-extension of the quotient in the sy >= 3 branches.

(defun dqip-q-zero-update-body-p (q2 q1 index sx sy adjust)
  (implies
   (and (dqip-same-shape-p q2 q1)
        (dqip-update-p q2 q1 (+ (dqip-offset q2) index) 0)
        (equal (dqip-pelts q2 (+ (dqip-offset q2) index)) 0))
   (equal
    (dqip-value q2 (+ (- sx sy) 1))
    (dqip-value q1 (+ (- sx sy) adjust)))))

(defun-sk dqip-all-q-zero-updates-p (q1 index sx sy adjust)
  (forall (q2)
    (implies
     (dqip-ptr-p q2)
     (dqip-q-zero-update-body-p q2 q1 index sx sy adjust))))

(defun dqip-q-index-body-p (index-word q1 sx sy adjust)
  (implies
   (equal (dqip-sint32 index-word) (- sx sy))
   (and
    (dqip-bounds-at-p q1 (dqip-sint32 index-word))
    (equal (dqip-writable q1) t)
    (dqip-all-q-zero-updates-p
     q1 (dqip-sint32 index-word) sx sy adjust))))

(defun-sk dqip-all-q-indices-p (q1 sx sy adjust)
  (forall (index-word)
    (implies
     (dqip-bv32-p index-word)
     (dqip-q-index-body-p index-word q1 sx sy adjust))))

(defun dqip-q-flag-body-p (flag q1 sx sy adjust)
  (implies
   (and
    (implies (equal adjust 0) (equal flag t))
    (implies (equal flag t) (equal adjust 0)))
   (if (equal flag t)
       (and
        (dqip-int32-in-bounds-p (- sx sy))
        (dqip-all-q-indices-p q1 sx sy adjust))
     (equal
      (dqip-value q1 (+ (- sx sy) 1))
      (dqip-value q1 (+ (- sx sy) adjust))))))

(defun-sk dqip-all-q-flags-p (q1 sx sy adjust)
  (forall (flag)
    (implies
     (booleanp flag)
     (dqip-q-flag-body-p flag q1 sx sy adjust))))

(defun dqip-final-q2-body-p (q2 q1 x y remainder sx sy adjust)
  (implies
   (and
    (dqip-same-shape-p q2 q1)
    (equal
     (dqip-value q2 (+ (- sx sy) 1))
     (dqip-value q1 (+ (- sx sy) adjust))))
   (dqip-final-result-p x q2 y remainder sx sy)))

(defun-sk dqip-all-final-q2-p (q1 x y remainder sx sy adjust)
  (forall (q2)
    (implies
     (dqip-ptr-p q2)
     (dqip-final-q2-body-p q2 q1 x y remainder sx sy adjust))))

(defun dqip-q-adjust-p (q1 x y remainder sx sy adjust)
  (and
   (dqip-all-q-flags-p q1 sx sy adjust)
   (dqip-all-final-q2-p q1 x y remainder sx sy adjust)))

;; sy = 1 branch.

(defun dqip-one-x1-body-p (x1 x q1 y lr sx sy)
  (implies
   (and
    (dqip-same-shape-p x1 x)
    (dqip-update-p x1 x (dqip-offset x1) lr))
   (dqip-final-result-p x q1 y x1 sx sy)))

(defun-sk dqip-one-all-x1-p (x q1 y lr sx sy)
  (forall (x1)
    (implies
     (dqip-ptr-p x1)
     (dqip-one-x1-body-p x1 x q1 y lr sx sy))))

(defun dqip-one-lr-body-p (lr x q1 y divisor sx sy)
  (implies
   (and
    (equal
     (dqip-value x sx)
     (+ (* (dqip-value q1 sx) divisor) lr))
    (< lr divisor))
   (and
    (dqip-bounds-at-p x 0)
    (equal (dqip-writable x) t)
    (dqip-one-all-x1-p x q1 y lr sx sy))))

(defun-sk dqip-one-all-lr-p (x q1 y divisor sx sy)
  (forall (lr)
    (implies
     (dqip-bv64-p lr)
     (dqip-one-lr-body-p lr x q1 y divisor sx sy))))

(defun dqip-one-q1-body-p (q1 q x y divisor sx sy)
  (implies
   (dqip-same-shape-p q1 q)
   (dqip-one-all-lr-p x q1 y divisor sx sy)))

(defun-sk dqip-one-all-q1-p (q x y divisor sx sy)
  (forall (q1)
    (implies
     (dqip-ptr-p q1)
     (dqip-one-q1-body-p q1 q x y divisor sx sy))))

(defun dqip-one-branch-p (q x y sx sy)
  (let ((divisor (dqip-pelts y (dqip-offset y))))
    (and
     (dqip-bounds-at-p y 0)
     (dqip-valid-p x sx)
     (dqip-valid-p q sx)
     (equal (dqip-writable q) t)
     (< 0 sx)
     (< 0 divisor)
     (dqip-one-all-q1-p q x y divisor sx sy))))

;; Common division continuation used by the normalized two-limb branches.

(defun dqip-two-x1-body-p (x1 x nx3 q1 y sx sy)
  (implies
   (and
    (dqip-same-shape-p x1 x)
    (dqip-copy-p x1 nx3 x sy))
   (dqip-final-result-p x q1 y x1 sx sy)))

(defun-sk dqip-two-all-x1-p (x nx3 q1 y sx sy)
  (forall (x1)
    (implies
     (dqip-ptr-p x1)
     (dqip-two-x1-body-p x1 x nx3 q1 y sx sy))))

(defun dqip-two-xqh-body-p (xqh nx2 nx3 q1 x y divisor size sx sy)
  (implies
   (and
    (equal
     (dqip-value nx2 size)
     (+ (* (+ (dqip-value q1 (- size 2))
              (* (dqip-ipow *dqip-radix* (- size 2)) xqh))
           (dqip-value divisor 2))
        (dqip-value nx3 2)))
    (< (dqip-value nx3 2) (dqip-value divisor 2))
    (<= 0 xqh)
    (<= xqh 1))
   (and
    (dqip-valid-p nx3 sy)
    (dqip-valid-p x sy)
    (equal (dqip-writable x) t)
    (dqip-two-all-x1-p x nx3 q1 y sx sy))))

(defun-sk dqip-two-all-xqh-p
    (nx2 nx3 q1 x y divisor size sx sy)
  (forall (xqh)
    (implies
     (dqip-bv64-p xqh)
     (dqip-two-xqh-body-p
      xqh nx2 nx3 q1 x y divisor size sx sy))))

(defun dqip-two-q1-body-p (q1 q nx2 nx3 x y divisor size sx sy)
  (implies
   (dqip-same-shape-p q1 q)
   (dqip-two-all-xqh-p nx2 nx3 q1 x y divisor size sx sy)))

(defun-sk dqip-two-all-q1-p (q nx2 nx3 x y divisor size sx sy)
  (forall (q1)
    (implies
     (dqip-ptr-p q1)
     (dqip-two-q1-body-p q1 q nx2 nx3 x y divisor size sx sy))))

(defun dqip-two-nx3-body-p (nx3 nx2 q x y divisor size sx sy)
  (implies
   (dqip-same-shape-p nx3 nx2)
   (dqip-two-all-q1-p q nx2 nx3 x y divisor size sx sy)))

(defun-sk dqip-two-all-nx3-p (nx2 q x y divisor size sx sy)
  (forall (nx3)
    (implies
     (dqip-ptr-p nx3)
     (dqip-two-nx3-body-p nx3 nx2 q x y divisor size sx sy))))

(defun dqip-two-size-body-p
    (size-word nx2 q x y divisor sx sy)
  (let ((size (dqip-sint32 size-word)))
    (implies
     (equal size (+ sx 1))
     (and
      (<= 2 size)
      (dqip-valid-p nx2 size)
      (dqip-valid-p divisor 2)
      (dqip-valid-p q (- size 2))
      (<= (floor *dqip-radix* 2)
          (dqip-pelts divisor (+ (dqip-offset divisor) 1)))
      (equal (dqip-writable q) t)
      (equal (dqip-writable nx2) t)
      (dqip-two-all-nx3-p nx2 q x y divisor size sx sy)))))

(defun-sk dqip-two-all-sizes-p (nx2 q x y divisor sx sy)
  (forall (size-word)
    (implies
     (dqip-bv32-p size-word)
     (dqip-two-size-body-p size-word nx2 q x y divisor sx sy))))

;; sy = 2, clz = 0: copy x to nx, append a zero limb, and divide by y.

(defun dqip-two-zero-nx2-body-p (nx2 nx1 q x y sx sy)
  (implies
   (and
    (dqip-same-shape-p nx2 nx1)
    (dqip-update-p nx2 nx1 (+ (dqip-offset nx2) sx) 0)
    (equal (dqip-pelts nx2 (+ (dqip-offset nx2) sx)) 0))
   (and
    (dqip-int32-in-bounds-p (+ sx 1))
    (dqip-two-all-sizes-p nx2 q x y y sx sy))))

(defun-sk dqip-two-zero-all-nx2-p (nx1 q x y sx sy)
  (forall (nx2)
    (implies
     (dqip-ptr-p nx2)
     (dqip-two-zero-nx2-body-p nx2 nx1 q x y sx sy))))

(defun dqip-two-zero-nx1-body-p (nx1 nx q x y sx sy)
  (implies
   (and
    (dqip-same-shape-p nx1 nx)
    (dqip-copy-p nx1 x nx sx))
   (and
    (dqip-bounds-at-p nx1 sx)
    (equal (dqip-writable nx1) t)
    (dqip-two-zero-all-nx2-p nx1 q x y sx sy))))

(defun-sk dqip-two-zero-all-nx1-p (nx q x y sx sy)
  (forall (nx1)
    (implies
     (dqip-ptr-p nx1)
     (dqip-two-zero-nx1-body-p nx1 nx q x y sx sy))))

(defun dqip-two-zero-p (nx q x y sx sy)
  (and
   (dqip-valid-p x sx)
   (dqip-valid-p nx sx)
   (equal (dqip-writable nx) t)
   (dqip-two-zero-all-nx1-p nx q x y sx sy)))

;; sy = 2, clz > 0: normalize y and x, divide, then right-shift the remainder.

(defun dqip-two-shift-xl-body-p
    (xl x1 x nx3 q1 y p sx sy clz-word)
  (implies
   (equal
    (+ xl (* *dqip-radix* (dqip-value x1 sy)))
    (* (dqip-value nx3 sy)
       (dqip-ipow 2 (- 64 clz-word))))
   (and
    (equal (dqip-value nx3 2) (* p (dqip-value x1 2)))
    (implies
     (equal (dqip-value nx3 2) (* p (dqip-value x1 2)))
     (dqip-final-result-p x q1 y x1 sx sy)))))

(defun-sk dqip-two-shift-all-xl-p
    (x1 x nx3 q1 y p sx sy clz-word)
  (forall (xl)
    (implies
     (dqip-bv64-p xl)
     (dqip-two-shift-xl-body-p
      xl x1 x nx3 q1 y p sx sy clz-word))))

(defun dqip-two-shift-x1-body-p (x1 x nx3 q1 y p sx sy clz-word)
  (implies
   (dqip-same-shape-p x1 x)
   (dqip-two-shift-all-xl-p
    x1 x nx3 q1 y p sx sy clz-word)))

(defun-sk dqip-two-shift-all-x1-p (x nx3 q1 y p sx sy clz-word)
  (forall (x1)
    (implies
     (dqip-ptr-p x1)
     (dqip-two-shift-x1-body-p x1 x nx3 q1 y p sx sy clz-word))))

(defun dqip-two-shift-o9-body-p
    (o9 nx3 q1 x y p sx sy clz)
  (implies
   (equal o9 clz)
   (and
    (dqip-valid-p nx3 sy)
    (dqip-valid-p x sy)
    (< 0 o9)
    (< o9 64)
    (< 0 sy)
    (equal (dqip-writable x) t)
    (dqip-two-shift-all-x1-p x nx3 q1 y p sx sy o9))))

(defun-sk dqip-two-shift-all-o9-p
    (nx3 q1 x y p sx sy clz)
  (forall (o9)
    (implies
     (dqip-bv64-p o9)
     (dqip-two-shift-o9-body-p
      o9 nx3 q1 x y p sx sy clz))))

(defun dqip-two-shift-xqh-body-p
    (xqh nx2 nx3 q1 x y ny1 p size sx sy clz)
  (implies
   (and
    (equal
     (dqip-value nx2 size)
     (+ (* (+ (dqip-value q1 (- size 2))
              (* (dqip-ipow *dqip-radix* (- size 2)) xqh))
           (dqip-value ny1 2))
        (dqip-value nx3 2)))
    (< (dqip-value nx3 2) (dqip-value ny1 2))
    (<= 0 xqh)
    (<= xqh 1))
   (and
    (<= 0 clz)
    (dqip-two-shift-all-o9-p
     nx3 q1 x y p sx sy clz))))

(defun-sk dqip-two-shift-all-xqh-p
    (nx2 nx3 q1 x y ny1 p size sx sy clz)
  (forall (xqh)
    (implies
     (dqip-bv64-p xqh)
     (dqip-two-shift-xqh-body-p
      xqh nx2 nx3 q1 x y ny1 p size sx sy clz))))

(defun dqip-two-shift-q1-body-p
    (q1 q nx2 nx3 x y ny1 p size sx sy clz)
  (implies
   (dqip-same-shape-p q1 q)
   (dqip-two-shift-all-xqh-p
    nx2 nx3 q1 x y ny1 p size sx sy clz)))

(defun-sk dqip-two-shift-all-q1-p
    (q nx2 nx3 x y ny1 p size sx sy clz)
  (forall (q1)
    (implies
     (dqip-ptr-p q1)
     (dqip-two-shift-q1-body-p
      q1 q nx2 nx3 x y ny1 p size sx sy clz))))

(defun dqip-two-shift-nx3-body-p
    (nx3 nx2 q x y ny1 p size sx sy clz)
  (implies
   (dqip-same-shape-p nx3 nx2)
   (dqip-two-shift-all-q1-p
    q nx2 nx3 x y ny1 p size sx sy clz)))

(defun-sk dqip-two-shift-all-nx3-p
    (nx2 q x y ny1 p size sx sy clz)
  (forall (nx3)
    (implies
     (dqip-ptr-p nx3)
     (dqip-two-shift-nx3-body-p
      nx3 nx2 q x y ny1 p size sx sy clz))))

(defun dqip-two-shift-size-body-p
    (size-word nx2 q x y ny1 p sx sy clz)
  (let ((size (dqip-sint32 size-word)))
    (implies
     (equal size (+ sx 1))
     (and
      (<= 2 size)
      (dqip-valid-p nx2 size)
      (dqip-valid-p ny1 2)
      (dqip-valid-p q (- size 2))
      (<= (floor *dqip-radix* 2)
          (dqip-pelts ny1 (+ (dqip-offset ny1) 1)))
      (equal (dqip-writable q) t)
      (equal (dqip-writable nx2) t)
      (dqip-two-shift-all-nx3-p
       nx2 q x y ny1 p size sx sy clz)))))

(defun-sk dqip-two-shift-all-sizes-p
    (nx2 q x y ny1 p sx sy clz)
  (forall (size-word)
    (implies
     (dqip-bv32-p size-word)
     (dqip-two-shift-size-body-p
      size-word nx2 q x y ny1 p sx sy clz))))

(defun dqip-two-shift-nx2-body-p
    (nx2 nx1 q x y ny1 p sx sy clz h)
  (implies
   (and
    (dqip-same-shape-p nx2 nx1)
    (dqip-update-p nx2 nx1 (+ (dqip-offset nx2) sx) h)
    (equal (dqip-pelts nx2 (+ (dqip-offset nx2) sx)) h))
   (and
    (equal (dqip-value nx2 (+ sx 1)) (* p (dqip-value x sx)))
    (implies
     (equal (dqip-value nx2 (+ sx 1)) (* p (dqip-value x sx)))
     (and
      (dqip-int32-in-bounds-p (+ sx 1))
      (dqip-two-shift-all-sizes-p
       nx2 q x y ny1 p sx sy clz))))))

(defun-sk dqip-two-shift-all-nx2-p
    (nx1 q x y ny1 p sx sy clz h)
  (forall (nx2)
    (implies
     (dqip-ptr-p nx2)
     (dqip-two-shift-nx2-body-p
      nx2 nx1 q x y ny1 p sx sy clz h))))

(defun dqip-two-shift-h-body-p
    (h nx1 q x y ny1 p sx sy clz o7)
  (implies
   (equal
    (+ (dqip-value nx1 sx)
       (* (dqip-ipow *dqip-radix* sx) h))
    (* (dqip-value x sx) (dqip-ipow 2 o7)))
   (and
    (dqip-bounds-at-p nx1 sx)
    (equal (dqip-writable nx1) t)
    (dqip-two-shift-all-nx2-p
     nx1 q x y ny1 p sx sy clz h))))

(defun-sk dqip-two-shift-all-h-p
    (nx1 q x y ny1 p sx sy clz o7)
  (forall (h)
    (implies
     (dqip-bv64-p h)
     (dqip-two-shift-h-body-p
      h nx1 q x y ny1 p sx sy clz o7))))

(defun dqip-two-shift-nx1-body-p
    (nx1 nx q x y ny1 p sx sy clz o7)
  (implies
   (dqip-same-shape-p nx1 nx)
   (dqip-two-shift-all-h-p
    nx1 q x y ny1 p sx sy clz o7)))

(defun-sk dqip-two-shift-all-nx1-p
    (nx q x y ny1 p sx sy clz o7)
  (forall (nx1)
    (implies
     (dqip-ptr-p nx1)
     (dqip-two-shift-nx1-body-p
      nx1 nx q x y ny1 p sx sy clz o7))))

(defun dqip-two-shift-o7-body-p
    (o7 nx q x y ny1 p sx sy clz)
  (implies
   (equal o7 clz)
   (and
    (< 0 o7)
    (< o7 64)
    (dqip-valid-p nx sx)
    (dqip-valid-p x sx)
    (equal (dqip-writable nx) t)
    (< 0 sx)
    (dqip-two-shift-all-nx1-p
     nx q x y ny1 p sx sy clz o7))))

(defun-sk dqip-two-shift-all-o7-p
    (nx q x y ny1 p sx sy clz)
  (forall (o7)
    (implies
     (dqip-bv64-p o7)
     (dqip-two-shift-o7-body-p
      o7 nx q x y ny1 p sx sy clz))))

(defun dqip-two-shift-xc-body-p
    (xc nx q x y ny1 p sx sy clz o6)
  (implies
   (equal
    (+ (dqip-value ny1 sy)
       (* (dqip-ipow *dqip-radix* sy) xc))
    (* (dqip-value y sy) (dqip-ipow 2 o6)))
   (let ((normalized-value
          (and
           (dqip-normalized-p ny1 sy)
           (equal
            (dqip-value ny1 sy)
            (* p (dqip-value y sy))))))
     (and
      normalized-value
      (implies
       normalized-value
       (and
        (<= 0 clz)
        (dqip-two-shift-all-o7-p
         nx q x y ny1 p sx sy clz)))))))

(defun-sk dqip-two-shift-all-xc-p
    (nx q x y ny1 p sx sy clz o6)
  (forall (xc)
    (implies
     (dqip-bv64-p xc)
     (dqip-two-shift-xc-body-p
      xc nx q x y ny1 p sx sy clz o6))))

(defun dqip-two-shift-ny1-body-p
    (ny1 ny nx q x y p sx sy clz o6)
  (implies
   (dqip-same-shape-p ny1 ny)
   (dqip-two-shift-all-xc-p
    nx q x y ny1 p sx sy clz o6)))

(defun-sk dqip-two-shift-all-ny1-p
    (ny nx q x y p sx sy clz o6)
  (forall (ny1)
    (implies
     (dqip-ptr-p ny1)
     (dqip-two-shift-ny1-body-p
      ny1 ny nx q x y p sx sy clz o6))))

(defun dqip-two-shift-o6-body-p
    (o6 ny nx q x y p sx sy clz)
  (implies
   (equal o6 clz)
   (and
    (< 0 o6)
    (< o6 64)
    (dqip-valid-p ny sy)
    (dqip-valid-p y sy)
    (equal (dqip-writable ny) t)
    (< 0 sy)
    (dqip-two-shift-all-ny1-p
     ny nx q x y p sx sy clz o6))))

(defun-sk dqip-two-shift-all-o6-p
    (ny nx q x y p sx sy clz)
  (forall (o6)
    (implies
     (dqip-bv64-p o6)
     (dqip-two-shift-o6-body-p
      o6 ny nx q x y p sx sy clz))))

(defun dqip-two-nonzero-p (ny nx q x y p sx sy clz)
  (and
   (<= 0 clz)
   (dqip-two-shift-all-o6-p ny nx q x y p sx sy clz)))

;; General sy >= 3 branch.

(defun dqip-general-x1-copy-body-p
    (x1 x nx3 q1 y sx sy adjust)
  (implies
   (and
    (dqip-same-shape-p x1 x)
    (dqip-copy-p x1 nx3 x sy))
   (dqip-q-adjust-p q1 x y x1 sx sy adjust)))

(defun-sk dqip-general-all-x1-copy-p
    (x nx3 q1 y sx sy adjust)
  (forall (x1)
    (implies
     (dqip-ptr-p x1)
     (dqip-general-x1-copy-body-p
      x1 x nx3 q1 y sx sy adjust))))

(defun dqip-general-xqh-copy-body-p
    (xqh nx2 nx3 q1 x y size sx sy adjust)
  (implies
   (and
    (equal
     (dqip-value nx2 size)
     (+ (* (+ (dqip-value q1 (- size sy))
              (* (dqip-ipow *dqip-radix* (- size sy)) xqh))
           (dqip-value y sy))
        (dqip-value nx3 sy)))
    (< (dqip-value nx3 sy) (dqip-value y sy))
    (<= 0 xqh)
    (<= xqh 1))
   (and
    (dqip-valid-p nx3 sy)
    (dqip-valid-p x sy)
    (equal (dqip-writable x) t)
    (dqip-general-all-x1-copy-p
     x nx3 q1 y sx sy adjust))))

(defun-sk dqip-general-all-xqh-copy-p
    (nx2 nx3 q1 x y size sx sy adjust)
  (forall (xqh)
    (implies
     (dqip-bv64-p xqh)
     (dqip-general-xqh-copy-body-p
      xqh nx2 nx3 q1 x y size sx sy adjust))))

(defun dqip-general-q1-copy-body-p
    (q1 q nx2 nx3 x y size sx sy adjust)
  (implies
   (dqip-same-shape-p q1 q)
   (dqip-general-all-xqh-copy-p
    nx2 nx3 q1 x y size sx sy adjust)))

(defun-sk dqip-general-all-q1-copy-p
    (q nx2 nx3 x y size sx sy adjust)
  (forall (q1)
    (implies
     (dqip-ptr-p q1)
     (dqip-general-q1-copy-body-p
      q1 q nx2 nx3 x y size sx sy adjust))))

(defun dqip-general-nx3-copy-body-p
    (nx3 nx2 q x y size sx sy adjust)
  (implies
   (dqip-same-shape-p nx3 nx2)
   (dqip-general-all-q1-copy-p
    q nx2 nx3 x y size sx sy adjust)))

(defun-sk dqip-general-all-nx3-copy-p
    (nx2 q x y size sx sy adjust)
  (forall (nx3)
    (implies
     (dqip-ptr-p nx3)
     (dqip-general-nx3-copy-body-p
      nx3 nx2 q x y size sx sy adjust))))

(defun dqip-general-size-copy-body-p
    (size-word nx2 q x y sx sy adjust)
  (let ((size (dqip-sint32 size-word)))
    (implies
     (equal size (+ sx adjust))
     (and
      (<= 3 sy)
      (<= sy size)
      (dqip-valid-p nx2 size)
      (dqip-valid-p y sy)
      (dqip-valid-p q (- size sy))
      (equal (dqip-writable q) t)
      (equal (dqip-writable nx2) t)
      (dqip-normalized-p y sy)
      (dqip-general-all-nx3-copy-p
       nx2 q x y size sx sy adjust)))))

(defun-sk dqip-general-all-size-copy-p
    (nx2 q x y sx sy adjust)
  (forall (size-word)
    (implies
     (dqip-bv32-p size-word)
     (dqip-general-size-copy-body-p
      size-word nx2 q x y sx sy adjust))))

(defun dqip-general-zero-nx2-body-p
    (nx2 nx1 q x y sx sy adjust)
  (implies
   (and
    (dqip-same-shape-p nx2 nx1)
    (dqip-update-p nx2 nx1 (+ (dqip-offset nx2) sx) 0)
    (equal (dqip-pelts nx2 (+ (dqip-offset nx2) sx)) 0))
   (and
    (dqip-int32-in-bounds-p (+ sx adjust))
    (dqip-general-all-size-copy-p
     nx2 q x y sx sy adjust))))

(defun-sk dqip-general-zero-all-nx2-p
    (nx1 q x y sx sy adjust)
  (forall (nx2)
    (implies
     (dqip-ptr-p nx2)
     (dqip-general-zero-nx2-body-p
      nx2 nx1 q x y sx sy adjust))))

(defun dqip-general-zero-nx1-body-p
    (nx1 nx q x y sx sy adjust)
  (implies
   (and
    (dqip-same-shape-p nx1 nx)
    (dqip-copy-p nx1 x nx sx))
   (and
    (dqip-bounds-at-p nx1 sx)
    (equal (dqip-writable nx1) t)
    (dqip-general-zero-all-nx2-p
     nx1 q x y sx sy adjust))))

(defun-sk dqip-general-zero-all-nx1-p
    (nx q x y sx sy adjust)
  (forall (nx1)
    (implies
     (dqip-ptr-p nx1)
     (dqip-general-zero-nx1-body-p
      nx1 nx q x y sx sy adjust))))

(defun dqip-general-zero-p (nx q x y sx sy adjust)
  (and
   (dqip-valid-p x sx)
   (dqip-valid-p nx sx)
   (equal (dqip-writable nx) t)
   (dqip-general-zero-all-nx1-p nx q x y sx sy adjust)))

;; General nonzero normalization branch.

(defun dqip-general-shift-xl-body-p
    (xl x1 x nx3 q1 y p sx sy adjust o12)
  (implies
   (equal
    (+ xl (* *dqip-radix* (dqip-value x1 sy)))
    (* (dqip-value nx3 sy)
       (dqip-ipow 2 (- 64 o12))))
   (and
    (equal (dqip-value nx3 sy) (* p (dqip-value x1 sy)))
    (implies
     (equal (dqip-value nx3 sy) (* p (dqip-value x1 sy)))
     (dqip-q-adjust-p q1 x y x1 sx sy adjust)))))

(defun-sk dqip-general-shift-all-xl-p
    (x1 x nx3 q1 y p sx sy adjust o12)
  (forall (xl)
    (implies
     (dqip-bv64-p xl)
     (dqip-general-shift-xl-body-p
      xl x1 x nx3 q1 y p sx sy adjust o12))))

(defun dqip-general-shift-x1-body-p
    (x1 x nx3 q1 y p sx sy adjust o12)
  (implies
   (dqip-same-shape-p x1 x)
   (dqip-general-shift-all-xl-p
    x1 x nx3 q1 y p sx sy adjust o12)))

(defun-sk dqip-general-shift-all-x1-p
    (x nx3 q1 y p sx sy adjust o12)
  (forall (x1)
    (implies
     (dqip-ptr-p x1)
     (dqip-general-shift-x1-body-p
      x1 x nx3 q1 y p sx sy adjust o12))))

(defun dqip-general-shift-o12-body-p
    (o12 nx3 q1 x y p sx sy adjust clz)
  (implies
   (equal o12 clz)
   (and
    (dqip-valid-p nx3 sy)
    (dqip-valid-p x sy)
    (< 0 o12)
    (< o12 64)
    (< 0 sy)
    (equal (dqip-writable x) t)
    (dqip-general-shift-all-x1-p
     x nx3 q1 y p sx sy adjust o12))))

(defun-sk dqip-general-shift-all-o12-p
    (nx3 q1 x y p sx sy adjust clz)
  (forall (o12)
    (implies
     (dqip-bv64-p o12)
     (dqip-general-shift-o12-body-p
      o12 nx3 q1 x y p sx sy adjust clz))))

(defun dqip-general-shift-xqh-body-p
    (xqh nx2 nx3 q1 x y ny1 p size sx sy adjust clz)
  (implies
   (and
    (equal
     (dqip-value nx2 size)
     (+ (* (+ (dqip-value q1 (- size sy))
              (* (dqip-ipow *dqip-radix* (- size sy)) xqh))
           (dqip-value ny1 sy))
        (dqip-value nx3 sy)))
    (< (dqip-value nx3 sy) (dqip-value ny1 sy))
    (<= 0 xqh)
    (<= xqh 1))
   (and
    (<= 0 clz)
    (dqip-general-shift-all-o12-p
     nx3 q1 x y p sx sy adjust clz))))

(defun-sk dqip-general-shift-all-xqh-p
    (nx2 nx3 q1 x y ny1 p size sx sy adjust clz)
  (forall (xqh)
    (implies
     (dqip-bv64-p xqh)
     (dqip-general-shift-xqh-body-p
      xqh nx2 nx3 q1 x y ny1 p size sx sy adjust clz))))

(defun dqip-general-shift-q1-body-p
    (q1 q nx2 nx3 x y ny1 p size sx sy adjust clz)
  (implies
   (dqip-same-shape-p q1 q)
   (dqip-general-shift-all-xqh-p
    nx2 nx3 q1 x y ny1 p size sx sy adjust clz)))

(defun-sk dqip-general-shift-all-q1-p
    (q nx2 nx3 x y ny1 p size sx sy adjust clz)
  (forall (q1)
    (implies
     (dqip-ptr-p q1)
     (dqip-general-shift-q1-body-p
      q1 q nx2 nx3 x y ny1 p size sx sy adjust clz))))

(defun dqip-general-shift-nx3-body-p
    (nx3 nx2 q x y ny1 p size sx sy adjust clz)
  (implies
   (dqip-same-shape-p nx3 nx2)
   (dqip-general-shift-all-q1-p
    q nx2 nx3 x y ny1 p size sx sy adjust clz)))

(defun-sk dqip-general-shift-all-nx3-p
    (nx2 q x y ny1 p size sx sy adjust clz)
  (forall (nx3)
    (implies
     (dqip-ptr-p nx3)
     (dqip-general-shift-nx3-body-p
      nx3 nx2 q x y ny1 p size sx sy adjust clz))))

(defun dqip-general-shift-size-body-p
    (size-word nx2 q x y ny1 p sx sy adjust clz)
  (let ((size (dqip-sint32 size-word)))
    (implies
     (equal size (+ sx adjust))
     (and
      (<= 3 sy)
      (<= sy size)
      (dqip-valid-p nx2 size)
      (dqip-valid-p ny1 sy)
      (dqip-valid-p q (- size sy))
      (equal (dqip-writable q) t)
      (equal (dqip-writable nx2) t)
      (dqip-normalized-p ny1 sy)
      (dqip-general-shift-all-nx3-p
       nx2 q x y ny1 p size sx sy adjust clz)))))

(defun-sk dqip-general-shift-all-sizes-p
    (nx2 q x y ny1 p sx sy adjust clz)
  (forall (size-word)
    (implies
     (dqip-bv32-p size-word)
     (dqip-general-shift-size-body-p
      size-word nx2 q x y ny1 p sx sy adjust clz))))

(defun dqip-general-adjust-flag-body-p
    (flag nx2 q x y ny1 p sx sy adjust clz)
  (implies
   (and
    (implies (equal adjust 1) (equal flag t))
    (implies (equal flag t) (equal adjust 1)))
   (and
    (dqip-int32-in-bounds-p (+ sx adjust))
    (dqip-general-shift-all-sizes-p
     nx2 q x y ny1 p sx sy adjust clz))))

(defun-sk dqip-general-all-adjust-flags-p
    (nx2 q x y ny1 p sx sy adjust clz)
  (forall (flag)
    (implies
     (booleanp flag)
     (dqip-general-adjust-flag-body-p
      flag nx2 q x y ny1 p sx sy adjust clz))))

(defun dqip-general-shift-nx2-body-p
    (nx2 nx1 q x y ny1 p sx sy adjust clz h)
  (implies
   (and
    (dqip-same-shape-p nx2 nx1)
    (dqip-update-p nx2 nx1 (+ (dqip-offset nx2) sx) h)
    (equal (dqip-pelts nx2 (+ (dqip-offset nx2) sx)) h))
   (dqip-general-all-adjust-flags-p
    nx2 q x y ny1 p sx sy adjust clz)))

(defun-sk dqip-general-shift-all-nx2-p
    (nx1 q x y ny1 p sx sy adjust clz h)
  (forall (nx2)
    (implies
     (dqip-ptr-p nx2)
     (dqip-general-shift-nx2-body-p
      nx2 nx1 q x y ny1 p sx sy adjust clz h))))

(defun dqip-general-shift-h-body-p
    (h nx1 q x y ny1 p sx sy adjust clz o9)
  (implies
   (equal
    (+ (dqip-value nx1 sx)
       (* (dqip-ipow *dqip-radix* sx) h))
    (* (dqip-value x sx) (dqip-ipow 2 o9)))
   (and
    (dqip-bounds-at-p nx1 sx)
    (equal (dqip-writable nx1) t)
    (dqip-general-shift-all-nx2-p
     nx1 q x y ny1 p sx sy adjust clz h))))

(defun-sk dqip-general-shift-all-h-p
    (nx1 q x y ny1 p sx sy adjust clz o9)
  (forall (h)
    (implies
     (dqip-bv64-p h)
     (dqip-general-shift-h-body-p
      h nx1 q x y ny1 p sx sy adjust clz o9))))

(defun dqip-general-shift-nx1-body-p
    (nx1 nx q x y ny1 p sx sy adjust clz o9)
  (implies
   (dqip-same-shape-p nx1 nx)
   (dqip-general-shift-all-h-p
    nx1 q x y ny1 p sx sy adjust clz o9)))

(defun-sk dqip-general-shift-all-nx1-p
    (nx q x y ny1 p sx sy adjust clz o9)
  (forall (nx1)
    (implies
     (dqip-ptr-p nx1)
     (dqip-general-shift-nx1-body-p
      nx1 nx q x y ny1 p sx sy adjust clz o9))))

(defun dqip-general-shift-o9-body-p
    (o9 nx q x y ny1 p sx sy adjust clz)
  (implies
   (equal o9 clz)
   (and
    (< 0 o9)
    (< o9 64)
    (dqip-valid-p nx sx)
    (dqip-valid-p x sx)
    (equal (dqip-writable nx) t)
    (< 0 sx)
    (dqip-general-shift-all-nx1-p
     nx q x y ny1 p sx sy adjust clz o9))))

(defun-sk dqip-general-shift-all-o9-p
    (nx q x y ny1 p sx sy adjust clz)
  (forall (o9)
    (implies
     (dqip-bv64-p o9)
     (dqip-general-shift-o9-body-p
      o9 nx q x y ny1 p sx sy adjust clz))))

(defun dqip-general-shift-xc-body-p
    (xc ny1 nx q x y p sx sy adjust clz o8)
  (implies
   (equal
    (+ (dqip-value ny1 sy)
       (* (dqip-ipow *dqip-radix* sy) xc))
    (* (dqip-value y sy) (dqip-ipow 2 o8)))
   (and
    (<= 0 clz)
    (dqip-general-shift-all-o9-p
     nx q x y ny1 p sx sy adjust clz))))

(defun-sk dqip-general-shift-all-xc-p
    (ny1 nx q x y p sx sy adjust clz o8)
  (forall (xc)
    (implies
     (dqip-bv64-p xc)
     (dqip-general-shift-xc-body-p
      xc ny1 nx q x y p sx sy adjust clz o8))))

(defun dqip-general-shift-ny1-body-p
    (ny1 ny nx q x y p sx sy adjust clz o8)
  (implies
   (dqip-same-shape-p ny1 ny)
   (dqip-general-shift-all-xc-p
    ny1 nx q x y p sx sy adjust clz o8)))

(defun-sk dqip-general-shift-all-ny1-p
    (ny nx q x y p sx sy adjust clz o8)
  (forall (ny1)
    (implies
     (dqip-ptr-p ny1)
     (dqip-general-shift-ny1-body-p
      ny1 ny nx q x y p sx sy adjust clz o8))))

(defun dqip-general-shift-o8-body-p
    (o8 ny nx q x y p sx sy adjust clz)
  (implies
   (equal o8 clz)
   (and
    (< 0 o8)
    (< o8 64)
    (dqip-valid-p ny sy)
    (dqip-valid-p y sy)
    (equal (dqip-writable ny) t)
    (< 0 sy)
    (dqip-general-shift-all-ny1-p
     ny nx q x y p sx sy adjust clz o8))))

(defun-sk dqip-general-shift-all-o8-p
    (ny nx q x y p sx sy adjust clz)
  (forall (o8)
    (implies
     (dqip-bv64-p o8)
     (dqip-general-shift-o8-body-p
      o8 ny nx q x y p sx sy adjust clz))))

(defun dqip-general-nonzero-p
    (ny nx q x y p sx sy adjust clz)
  (and
   (<= 0 clz)
   (dqip-general-shift-all-o8-p
    ny nx q x y p sx sy adjust clz)))

;; Selection of clz and its zero/nonzero continuation.

(defun dqip-clz-conditions-p (clz top-limb)
  (and
   (< (* (dqip-ipow 2 clz) top-limb) *dqip-radix*)
   (<= *dqip-radix* (* 2 (dqip-ipow 2 clz) top-limb))
   (<= 0 clz)
   (< clz 64)
   (<= (* (dqip-ipow 2 clz) top-limb)
       (- *dqip-radix* (dqip-ipow 2 clz)))))

(defun dqip-general-clz-flag-body-p
    (flag ny nx q x y sx sy adjust clz)
  (implies
   (and
    (implies (equal clz 0) (equal flag t))
    (implies (equal flag t) (equal clz 0)))
   (let ((p (dqip-ipow 2 clz)))
     (if (equal flag t)
         (dqip-general-zero-p nx q x y sx sy adjust)
       (dqip-general-nonzero-p
        ny nx q x y p sx sy adjust clz)))))

(defun-sk dqip-general-all-clz-flags-p
    (ny nx q x y sx sy adjust clz)
  (forall (flag)
    (implies
     (booleanp flag)
     (dqip-general-clz-flag-body-p
      flag ny nx q x y sx sy adjust clz))))

(defun dqip-general-clz-body-p
    (clz ny nx q x y sx sy adjust top-limb)
  (implies
   (dqip-clz-conditions-p (dqip-sint32 clz) top-limb)
   (dqip-general-all-clz-flags-p
    ny nx q x y sx sy adjust (dqip-sint32 clz))))

(defun-sk dqip-general-all-clz-p
    (ny nx q x y sx sy adjust top-limb)
  (forall (clz)
    (implies
     (dqip-bv32-p clz)
     (dqip-general-clz-body-p
      clz ny nx q x y sx sy adjust top-limb))))

(defun dqip-general-o5-body-p
    (o5 ny nx q x y sx sy adjust)
  (implies
   (equal (dqip-sint32 o5) (- sy 1))
   (let ((top-limb
          (dqip-pelts y (+ (dqip-offset y) (dqip-sint32 o5)))))
     (and
      (dqip-bounds-at-p y (dqip-sint32 o5))
      (< 0 top-limb)
      (dqip-general-all-clz-p
       ny nx q x y sx sy adjust top-limb)))))

(defun-sk dqip-general-all-o5-p
    (ny nx q x y sx sy adjust)
  (forall (o5)
    (implies
     (dqip-bv32-p o5)
     (dqip-general-o5-body-p
      o5 ny nx q x y sx sy adjust))))

(defun dqip-general-adjust-body-p
    (adjust ny nx q x y sx sy o3 o4)
  (implies
   (equal
    adjust
    (if (<= (dqip-pelts y (+ (dqip-offset y) (dqip-sint32 o3)))
             (dqip-pelts x (+ (dqip-offset x) (dqip-sint32 o4))))
        1
      0))
   (and
    (dqip-int32-in-bounds-p (- sy 1))
    (dqip-general-all-o5-p
     ny nx q x y sx sy (dqip-sint32 adjust)))))

(defun-sk dqip-general-all-adjust-p
    (ny nx q x y sx sy o3 o4)
  (forall (adjust)
    (implies
     (dqip-bv32-p adjust)
     (dqip-general-adjust-body-p
      adjust ny nx q x y sx sy o3 o4))))

(defun dqip-general-o4-body-p
    (o4 ny nx q x y sx sy o3)
  (implies
   (equal (dqip-sint32 o4) (- sx 1))
   (and
    (dqip-bounds-at-p x (dqip-sint32 o4))
    (dqip-general-all-adjust-p
     ny nx q x y sx sy o3 o4))))

(defun-sk dqip-general-all-o4-p
    (ny nx q x y sx sy o3)
  (forall (o4)
    (implies
     (dqip-bv32-p o4)
     (dqip-general-o4-body-p
      o4 ny nx q x y sx sy o3))))

(defun dqip-general-o3-body-p
    (o3 ny nx q x y sx sy)
  (implies
   (equal (dqip-sint32 o3) (- sy 1))
   (and
    (dqip-bounds-at-p y (dqip-sint32 o3))
    (dqip-int32-in-bounds-p (- sx 1))
    (dqip-general-all-o4-p
     ny nx q x y sx sy o3))))

(defun-sk dqip-general-all-o3-p
    (ny nx q x y sx sy)
  (forall (o3)
    (implies
     (dqip-bv32-p o3)
     (dqip-general-o3-body-p
      o3 ny nx q x y sx sy))))

;; sy = 2 selection and clz continuation.

(defun dqip-two-clz-flag-body-p
    (flag ny nx q x y sx sy clz)
  (implies
   (and
    (implies (equal clz 0) (equal flag t))
    (implies (equal flag t) (equal clz 0)))
   (let ((p (dqip-ipow 2 clz)))
     (if (equal flag t)
         (dqip-two-zero-p nx q x y sx sy)
       (dqip-two-nonzero-p ny nx q x y p sx sy clz)))))

(defun-sk dqip-two-all-clz-flags-p
    (ny nx q x y sx sy clz)
  (forall (flag)
    (implies
     (booleanp flag)
     (dqip-two-clz-flag-body-p
      flag ny nx q x y sx sy clz))))

(defun dqip-two-clz-body-p
    (clz ny nx q x y sx sy top-limb)
  (implies
   (dqip-clz-conditions-p (dqip-sint32 clz) top-limb)
   (dqip-two-all-clz-flags-p
    ny nx q x y sx sy (dqip-sint32 clz))))

(defun-sk dqip-two-all-clz-p
    (ny nx q x y sx sy top-limb)
  (forall (clz)
    (implies
     (dqip-bv32-p clz)
     (dqip-two-clz-body-p
      clz ny nx q x y sx sy top-limb))))

(defun dqip-two-o3-body-p
    (o3 ny nx q x y sx sy)
  (implies
   (equal (dqip-sint32 o3) (- sy 1))
   (let ((top-limb
          (dqip-pelts y (+ (dqip-offset y) (dqip-sint32 o3)))))
     (and
      (dqip-bounds-at-p y (dqip-sint32 o3))
      (< 0 top-limb)
      (dqip-two-all-clz-p
       ny nx q x y sx sy top-limb)))))

(defun-sk dqip-two-all-o3-p
    (ny nx q x y sx sy)
  (forall (o3)
    (implies
     (dqip-bv32-p o3)
     (dqip-two-o3-body-p o3 ny nx q x y sx sy))))

(defun dqip-two-branch-p (ny nx q x y sx sy)
  (and
   (dqip-int32-in-bounds-p (- sy 1))
   (dqip-two-all-o3-p ny nx q x y sx sy)))

;; Outer indicator for sy = 2, followed by the top-level assumptions.

(defun dqip-sy2-flag-body-p
    (flag ny nx q x y sx sy)
  (implies
   (and
    (implies (equal sy 2) (equal flag t))
    (implies (equal flag t) (equal sy 2)))
   (if (equal flag t)
       (dqip-two-branch-p ny nx q x y sx sy)
     (and
      (dqip-int32-in-bounds-p (- sy 1))
      (dqip-general-all-o3-p ny nx q x y sx sy)))))

(defun-sk dqip-all-sy2-flags-p
    (ny nx q x y sx sy)
  (forall (flag)
    (implies
     (booleanp flag)
     (dqip-sy2-flag-body-p flag ny nx q x y sx sy))))

(defun dqip-top-body-p (syw sxw x y q nx ny one-flag)
  (let ((sy (dqip-sint32 syw))
        (sx (dqip-sint32 sxw)))
    (implies
     (and
      (<= 1 sy)
      (<= sy sx)
      (<= sx (- 2147483647 1))
      (dqip-valid-p x sx)
      (dqip-valid-p y sy)
      (dqip-valid-p q (+ (- sx sy) 1))
      (dqip-valid-p nx (+ sx 1))
      (dqip-valid-p ny sy)
      (equal (dqip-writable q) t)
      (equal (dqip-writable x) t)
      (equal (dqip-writable nx) t)
      (equal (dqip-writable ny) t)
      (< 0 (dqip-pelts y (- (+ (dqip-offset y) sy) 1)))
      (implies (equal sy 1) (equal one-flag t))
      (implies (equal one-flag t) (equal syw 1)))
     (if (equal one-flag t)
         (dqip-one-branch-p q x y sx sy)
       (dqip-all-sy2-flags-p ny nx q x y sx sy)))))

(defun-sk
    ntp4vc-pearl-multiprecision-div-div-div-qr-in-placeqtvc-statement
    ()
  (forall (syw sxw x y q nx ny one-flag)
    (implies
     (and
      (dqip-interface-p)
      (dqip-bv32-p syw)
      (dqip-bv32-p sxw)
      (dqip-ptr-p x)
      (dqip-ptr-p y)
      (dqip-ptr-p q)
      (dqip-ptr-p nx)
      (dqip-ptr-p ny)
      (booleanp one-flag))
     (dqip-top-body-p syw sxw x y q nx ny one-flag))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
