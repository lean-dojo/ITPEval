;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/div_Div_wmpn_divrem_1qtvc: the verification condition
;; for one-limb multi-precision division, including divisor normalization,
;; reciprocal division, quotient-array updates, loop invariants, and the final
;; quotient/remainder equation. This file contains no proof.

(in-package "ACL2")

(defconst *ddr1-radix* 18446744073709551616)
(defconst *ddr1-bv32-modulus* 4294967296)
(defconst *ddr1-bv32-sign* 2147483648)

;; Canonical integers represent fixed-width words bijectively.

(defun ddr1-bv64-p (x)
  (and (integerp x) (<= 0 x) (< x *ddr1-radix*)))

(defun ddr1-bv32-p (x)
  (and (integerp x) (<= 0 x) (< x *ddr1-bv32-modulus*)))

(defun ddr1-sint32 (x)
  (if (< x *ddr1-bv32-sign*)
      x
    (- x *ddr1-bv32-modulus*)))

(defun ddr1-int32-in-bounds-p (x)
  (and (integerp x)
       (<= (- *ddr1-bv32-sign*) x)
       (<= x (- *ddr1-bv32-sign* 1))))

(defun ddr1-uint64-in-bounds-p (x)
  (and (integerp x) (<= 0 x) (< x *ddr1-radix*)))

(defun ddr1-ipow (base exponent)
  (expt base (nfix exponent)))

;; The source pointer is represented by its complete statement-observable
;; tuple (data, offset, min, max, writable, zone).  Source array data has an
;; independent nonnegative length and a total integer-indexed limb map.  The
;; map term is either an arbitrary base token or a finite nest of updates.

(defun ddr1-data-p (data)
  (and (true-listp data)
       (equal (len data) 3)
       (equal (nth 0 data) :ddr1-data)
       (natp (nth 1 data))))

(defun ddr1-ptr-p (p)
  (and (true-listp p)
       (equal (len p) 7)
       (equal (nth 0 p) :ddr1-ptr)
       (ddr1-data-p (nth 1 p))
       (integerp (nth 2 p))
       (integerp (nth 3 p))
       (integerp (nth 4 p))
       (booleanp (nth 5 p))))

(defun ddr1-data (p) (nth 1 p))
(defun ddr1-data-length (p) (nth 1 (ddr1-data p)))
(defun ddr1-data-cells (p) (nth 2 (ddr1-data p)))
(defun ddr1-offset (p) (nth 2 p))
(defun ddr1-min (p) (nth 3 p))
(defun ddr1-max (p) (nth 4 p))
(defun ddr1-writable (p) (nth 5 p))
(defun ddr1-zone (p) (nth 6 p))

(defun ddr1-same-shape-p (new old)
  (and (equal (ddr1-data-length new) (ddr1-data-length old))
       (equal (ddr1-offset new) (ddr1-offset old))
       (equal (ddr1-min new) (ddr1-min old))
       (equal (ddr1-max new) (ddr1-max old))
       (equal (ddr1-writable new) (ddr1-writable old))
       (equal (ddr1-zone new) (ddr1-zone old))))

(defun ddr1-map-base (p)
  (ddr1-data-cells p))

(defun ddr1-map-update (map index value)
  (list :update map index value))

(defstub ddr1-base-map-get (map index) t)

(defun ddr1-map-get (map index)
  (declare (xargs :measure (acl2-count map)))
  (if (and (consp map) (equal (car map) :update))
      (if (equal index (caddr map))
          (cadddr map)
        (ddr1-map-get (cadr map) index))
    (let ((v (ddr1-base-map-get map index)))
      (if (ddr1-bv64-p v) v 0))))

(defun-sk ddr1-map-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal (ddr1-map-get left index)
            (ddr1-map-get right index)))))

(defun ddr1-valid-p (p size)
  (and (ddr1-int32-in-bounds-p size)
       (<= 0 size)
       (<= 0 (ddr1-min p))
       (<= (ddr1-min p) (ddr1-offset p))
       (<= (+ (ddr1-offset p) size) (ddr1-max p))
       (<= (ddr1-max p) (ddr1-data-length p))))

(defun ddr1-bounds-at-p (p index)
  (and (<= (ddr1-min p) (+ (ddr1-offset p) index))
       (< (+ (ddr1-offset p) index) (ddr1-max p))))

(defun ddr1-value-sub-count (map index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (ddr1-map-get map index)
       (* *ddr1-radix*
          (ddr1-value-sub-count map (+ index 1) (- count 1))))))

(defun ddr1-value-sub (map start end)
  (ddr1-value-sub-count map start (nfix (- end start))))

(defun ddr1-value (p size)
  (ddr1-value-sub
   (ddr1-map-base p)
   (ddr1-offset p)
   (+ (ddr1-offset p) size)))

(defun ddr1-reciprocal-p (v d)
  (equal
   v
   (-
    (floor (- (* *ddr1-radix* *ddr1-radix*) 1) d)
    *ddr1-radix*)))

(defun ddr1-normalized-loop-invariant-p
    (x sz q1 msb i r ry mult)
  (and
   (<= -1 (ddr1-sint32 i))
   (<= (ddr1-sint32 i) (ddr1-sint32 msb))
   (< r ry)
   (equal
    (* mult
       (ddr1-value-sub
        (ddr1-map-base x)
        (+ (ddr1-offset x) (ddr1-sint32 i) 1)
        (+ (ddr1-offset x) (ddr1-sint32 sz))))
    (+ (* (ddr1-value-sub
           (ddr1-map-base q1)
           (+ (ddr1-offset q1) (ddr1-sint32 i) 1)
           (+ (ddr1-offset q1) (ddr1-sint32 sz)))
          ry)
       r))
   (<= r (- *ddr1-radix* mult))
   (equal (mod r mult) 0)))

(defun ddr1-unnormalized-loop-invariant-p
    (x sz q1 msb i r y)
  (and
   (<= -1 (ddr1-sint32 i))
   (<= (ddr1-sint32 i) (ddr1-sint32 msb))
   (< r y)
   (equal
    (ddr1-value-sub
     (ddr1-map-base x)
     (+ (ddr1-offset x) (ddr1-sint32 i) 1)
     (+ (ddr1-offset x) (ddr1-sint32 sz)))
    (+ (* (ddr1-value-sub
           (ddr1-map-base q1)
           (+ (ddr1-offset q1) (ddr1-sint32 i) 1)
           (+ (ddr1-offset q1) (ddr1-sint32 sz)))
          y)
       r))))

;; All quantified variables below are universal. Pulling those quantifiers to
;; the front of each branch is equivalent to the source nesting because every
;; fixed-width and pointer domain is inhabited and each variable is fresh for
;; the antecedent across which it is moved.

#|
(defun-sk ddr1-normalized-branch-monolithic-p (x sz q y msb clz)
  (forall
   (o1 ry v r i q1 o2 l h o3 qu rem q2 o8 res o3n result)
   (implies
    (and
     (ddr1-bv64-p o1)
     (ddr1-bv64-p ry)
     (ddr1-bv64-p v)
     (ddr1-bv64-p r)
     (ddr1-bv32-p i)
     (ddr1-ptr-p q1)
     (ddr1-bv64-p o2)
     (ddr1-bv64-p l)
     (ddr1-bv64-p h)
     (ddr1-bv64-p o3)
     (ddr1-bv64-p qu)
     (ddr1-bv64-p rem)
     (ddr1-ptr-p q2)
     (ddr1-bv32-p o8)
     (ddr1-bv64-p res)
     (ddr1-bv64-p o3n)
     (ddr1-bv64-p result))
    (let ((clz-i (ddr1-sint32 clz))
          (mult (ddr1-ipow 2 (ddr1-sint32 clz))))
      (and
       (<= 0 clz-i)
       (implies
        (equal o1 clz-i)
        (and
         (<= 0 o1)
         (< o1 64)
         (<= (* (ddr1-ipow 2 o1) y) (- *ddr1-radix* 1))
         (implies
          (equal ry (* (ddr1-ipow 2 o1) y))
          (and
           (<= (floor *ddr1-radix* 2) ry)
           (implies
            (ddr1-reciprocal-p v ry)
            (and
             (<= -1 (ddr1-sint32 msb))
             (<= (ddr1-sint32 msb) (ddr1-sint32 msb))
             (< 0 ry)
             (equal
              (* mult
                 (ddr1-value-sub
                  (ddr1-map-base x)
                  (+ (ddr1-offset x) (ddr1-sint32 msb) 1)
                  (+ (ddr1-offset x) (ddr1-sint32 sz))))
              (* (ddr1-value-sub
                  (ddr1-map-base q)
                  (+ (ddr1-offset q) (ddr1-sint32 msb) 1)
                  (+ (ddr1-offset q) (ddr1-sint32 sz)))
                 ry))
             (<= 0 (- *ddr1-radix* mult))
             (equal (mod 0 mult) 0)
             (implies
              (ddr1-same-shape-p q1 q)
              (implies
               (ddr1-normalized-loop-invariant-p
                x sz q1 msb i r ry mult)
               (if (<= 0 (ddr1-sint32 i))
                   (and
                    (ddr1-bounds-at-p x (ddr1-sint32 i))
                    (<= 0 clz-i)
                    (implies
                     (equal o2 clz-i)
                     (and
                      (< 0 o2)
                      (< o2 64)
                      (implies
                       (and
                        (equal
                         (+ l (* *ddr1-radix* h))
                         (* (ddr1-ipow 2 o2)
                            (ddr1-map-get
                             (ddr1-map-base x)
                             (+ (ddr1-offset x) (ddr1-sint32 i)))))
                        (equal (mod l (ddr1-ipow 2 o2)) 0)
                        (<= l (- *ddr1-radix* (ddr1-ipow 2 o2)))
                        (< h (ddr1-ipow 2 o2)))
                       (and
                        (ddr1-uint64-in-bounds-p (+ r h))
                        (implies
                         (equal o3 (+ r h))
                         (and
                          (<= (floor *ddr1-radix* 2) ry)
                          (< o3 ry)
                          (ddr1-reciprocal-p v ry)
                          (implies
                           (and
                            (equal (+ (* qu ry) rem)
                                   (+ l (* *ddr1-radix* o3)))
                            (<= 0 rem)
                            (< rem ry))
                           (let* ((end (+ (ddr1-offset q1)
                                         (ddr1-sint32 sz)))
                                  (next (+ (ddr1-offset q1)
                                           1
                                           (ddr1-sint32 i)))
                                  (at (+ (ddr1-offset q1)
                                         (ddr1-sint32 i)))
                                  (base (ddr1-map-base q1)))
                             (and
                              (not (equal mult 0))
                              (<= next end)
                              (or (< at next) (<= end at))
                              (implies
                               (equal
                                (ddr1-value-sub base next end)
                                (ddr1-value-sub
                                 (ddr1-map-update base at qu)
                                 next end))
                               (and
                                (ddr1-bounds-at-p q1
                                                  (ddr1-sint32 i))
                                (equal (ddr1-writable q1) t)
                                (implies
                                 (ddr1-same-shape-p q2 q1)
                                 (implies
                                  (and
                                   (ddr1-map-equal-p
                                    (ddr1-map-base q2)
                                    (ddr1-map-update
                                     (ddr1-map-base q1)
                                     (+ (ddr1-offset q2)
                                        (ddr1-sint32 i))
                                     qu))
                                   (equal
                                    (ddr1-map-get
                                     (ddr1-map-base q2)
                                     (+ (ddr1-offset q2)
                                        (ddr1-sint32 i)))
                                    qu))
                                  (and
                                   (ddr1-int32-in-bounds-p
                                    (- (ddr1-sint32 i) 1))
                                   (implies
                                    (equal
                                     (ddr1-sint32 o8)
                                     (- (ddr1-sint32 i) 1))
                                    (and
                                     (< (ddr1-sint32 o8)
                                        (ddr1-sint32 i))
                                     (<= -1 (ddr1-sint32 o8))
                                     (<= (ddr1-sint32 o8)
                                         (ddr1-sint32 msb))
                                     (< rem ry)
                                     (equal
                                      (* mult
                                         (ddr1-value-sub
                                          (ddr1-map-base x)
                                          (+ (ddr1-offset x)
                                             (ddr1-sint32 o8)
                                             1)
                                          (+ (ddr1-offset x)
                                             (ddr1-sint32 sz))))
                                      (+ (* (ddr1-value-sub
                                             (ddr1-map-base q2)
                                             (+ (ddr1-offset q2)
                                                (ddr1-sint32 o8)
                                                1)
                                             (+ (ddr1-offset q2)
                                                (ddr1-sint32 sz)))
                                            ry)
                                         rem))
                                     (<= rem (- *ddr1-radix* mult))
                                     (equal (mod rem mult) 0))))))))))))))))))
                 (and
                  (<= 0 clz-i)
                  (implies
                   (equal o2 clz-i)
                   (and
                    (<= 0 o2)
                    (< o2 64)
                    (equal (mod r (ddr1-ipow 2 o2)) 0)
                    (implies
                     (equal r (* (ddr1-ipow 2 o2) res))
                     (and
                      (<= 0 clz-i)
                      (implies
                       (equal o3n clz-i)
                       (and
                        (<= 0 o3n)
                        (< o3n 64)
                        (equal (mod r (ddr1-ipow 2 o3n)) 0)
                        (implies
                         (equal r (* (ddr1-ipow 2 o3n) result))
                         (and
                          (equal
                           (ddr1-value x (ddr1-sint32 sz))
                           (+ (* (ddr1-value q1 (ddr1-sint32 sz))
                                 y)
                              result))
                          (< result y))))))))))))))))))))))))
|#

(defun-sk ddr1-normalized-update-p
    (x sz q1 msb i ry mult qu rem)
  (forall (q2 o8)
    (implies
     (and (ddr1-ptr-p q2) (ddr1-bv32-p o8))
     (let* ((end (+ (ddr1-offset q1) (ddr1-sint32 sz)))
            (next (+ (ddr1-offset q1) 1 (ddr1-sint32 i)))
            (at (+ (ddr1-offset q1) (ddr1-sint32 i)))
            (base (ddr1-map-base q1)))
       (and
        (not (equal mult 0))
        (<= next end)
        (or (< at next) (<= end at))
        (implies
         (equal
          (ddr1-value-sub base next end)
          (ddr1-value-sub (ddr1-map-update base at qu) next end))
         (and
          (ddr1-bounds-at-p q1 (ddr1-sint32 i))
          (equal (ddr1-writable q1) t)
          (implies
           (ddr1-same-shape-p q2 q1)
           (implies
            (and
             (ddr1-map-equal-p
              (ddr1-map-base q2)
              (ddr1-map-update
               (ddr1-map-base q1)
               (+ (ddr1-offset q2) (ddr1-sint32 i))
               qu))
             (equal
              (ddr1-map-get
               (ddr1-map-base q2)
               (+ (ddr1-offset q2) (ddr1-sint32 i)))
              qu))
            (and
             (ddr1-int32-in-bounds-p (- (ddr1-sint32 i) 1))
             (implies
              (equal (ddr1-sint32 o8) (- (ddr1-sint32 i) 1))
              (and
               (< (ddr1-sint32 o8) (ddr1-sint32 i))
               (<= -1 (ddr1-sint32 o8))
               (<= (ddr1-sint32 o8) (ddr1-sint32 msb))
               (< rem ry)
               (equal
                (* mult
                   (ddr1-value-sub
                    (ddr1-map-base x)
                    (+ (ddr1-offset x) (ddr1-sint32 o8) 1)
                    (+ (ddr1-offset x) (ddr1-sint32 sz))))
                (+ (* (ddr1-value-sub
                       (ddr1-map-base q2)
                       (+ (ddr1-offset q2) (ddr1-sint32 o8) 1)
                       (+ (ddr1-offset q2) (ddr1-sint32 sz)))
                      ry)
                   rem))
               (<= rem (- *ddr1-radix* mult))
               (equal (mod rem mult) 0)))))))))))))

(defun-sk ddr1-normalized-quotient-step-p
    (x sz q1 msb i r ry mult v l o3)
  (forall (qu rem)
    (implies
     (and (ddr1-bv64-p qu) (ddr1-bv64-p rem))
     (implies
      (and
       (equal (+ (* qu ry) rem) (+ l (* *ddr1-radix* o3)))
       (<= 0 rem)
       (< rem ry))
      (ddr1-normalized-update-p
       x sz q1 msb i ry mult qu rem)))))

(defun-sk ddr1-normalized-limb-step-p
    (x sz q1 msb clz i r ry mult v)
  (forall (l h o3)
    (implies
     (and (ddr1-bv64-p l)
          (ddr1-bv64-p h)
          (ddr1-bv64-p o3))
     (let ((shift (ddr1-sint32 clz)))
       (implies
        (and
         (equal
          (+ l (* *ddr1-radix* h))
          (* (ddr1-ipow 2 shift)
             (ddr1-map-get
              (ddr1-map-base x)
              (+ (ddr1-offset x) (ddr1-sint32 i)))))
         (equal (mod l (ddr1-ipow 2 shift)) 0)
         (<= l (- *ddr1-radix* (ddr1-ipow 2 shift)))
         (< h (ddr1-ipow 2 shift)))
        (and
         (ddr1-uint64-in-bounds-p (+ r h))
         (implies
          (equal o3 (+ r h))
          (and
           (<= (floor *ddr1-radix* 2) ry)
           (< o3 ry)
           (ddr1-reciprocal-p v ry)
           (ddr1-normalized-quotient-step-p
            x sz q1 msb i r ry mult v l o3)))))))))

(defun-sk ddr1-normalized-positive-p
    (x sz q1 msb clz i r ry mult v)
  (forall (o2)
    (implies
     (ddr1-bv64-p o2)
     (and
      (ddr1-bounds-at-p x (ddr1-sint32 i))
      (<= 0 (ddr1-sint32 clz))
      (implies
       (equal o2 (ddr1-sint32 clz))
       (and
        (< 0 o2)
        (< o2 64)
        (ddr1-normalized-limb-step-p
         x sz q1 msb clz i r ry mult v)))))))

(defun-sk ddr1-normalized-negative-p
    (x sz q1 y clz r)
  (forall (o2 res o3 result)
    (implies
     (and (ddr1-bv64-p o2)
          (ddr1-bv64-p res)
          (ddr1-bv64-p o3)
          (ddr1-bv64-p result))
     (and
      (<= 0 (ddr1-sint32 clz))
      (implies
       (equal o2 (ddr1-sint32 clz))
       (and
        (<= 0 o2)
        (< o2 64)
        (equal (mod r (ddr1-ipow 2 o2)) 0)
        (implies
         (equal r (* (ddr1-ipow 2 o2) res))
         (and
          (<= 0 (ddr1-sint32 clz))
          (implies
           (equal o3 (ddr1-sint32 clz))
           (and
            (<= 0 o3)
            (< o3 64)
            (equal (mod r (ddr1-ipow 2 o3)) 0)
            (implies
             (equal r (* (ddr1-ipow 2 o3) result))
             (and
              (equal
               (ddr1-value x (ddr1-sint32 sz))
               (+ (* (ddr1-value q1 (ddr1-sint32 sz)) y)
                  result))
             (< result y)))))))))))))

(defun-sk ddr1-normalized-loop-p
    (x sz q y msb clz ry mult v)
  (forall (r i q1)
    (implies
     (and (ddr1-bv64-p r)
          (ddr1-bv32-p i)
          (ddr1-ptr-p q1))
     (implies
      (ddr1-same-shape-p q1 q)
      (implies
       (ddr1-normalized-loop-invariant-p
        x sz q1 msb i r ry mult)
       (if (<= 0 (ddr1-sint32 i))
           (ddr1-normalized-positive-p
            x sz q1 msb clz i r ry mult v)
         (ddr1-normalized-negative-p x sz q1 y clz r)))))))

(defun-sk ddr1-normalized-v-p (x sz q y msb clz ry mult)
  (forall (v)
    (implies
     (ddr1-bv64-p v)
     (implies
      (ddr1-reciprocal-p v ry)
      (and
       (<= -1 (ddr1-sint32 msb))
       (<= (ddr1-sint32 msb) (ddr1-sint32 msb))
       (< 0 ry)
       (equal
        (* mult
           (ddr1-value-sub
            (ddr1-map-base x)
            (+ (ddr1-offset x) (ddr1-sint32 msb) 1)
            (+ (ddr1-offset x) (ddr1-sint32 sz))))
        (* (ddr1-value-sub
            (ddr1-map-base q)
            (+ (ddr1-offset q) (ddr1-sint32 msb) 1)
            (+ (ddr1-offset q) (ddr1-sint32 sz)))
           ry))
       (<= 0 (- *ddr1-radix* mult))
       (equal (mod 0 mult) 0)
       (ddr1-normalized-loop-p
        x sz q y msb clz ry mult v))))))

(defun-sk ddr1-normalized-ry-p (x sz q y msb clz mult o1)
  (forall (ry)
    (implies
     (ddr1-bv64-p ry)
     (implies
      (equal ry (* (ddr1-ipow 2 o1) y))
      (and
       (<= (floor *ddr1-radix* 2) ry)
       (ddr1-normalized-v-p x sz q y msb clz ry mult))))))

(defun-sk ddr1-normalized-branch-p (x sz q y msb clz)
  (forall (o1)
    (implies
     (ddr1-bv64-p o1)
     (let ((clz-i (ddr1-sint32 clz))
           (mult (ddr1-ipow 2 (ddr1-sint32 clz))))
       (and
        (<= 0 clz-i)
        (implies
         (equal o1 clz-i)
         (and
          (<= 0 o1)
          (< o1 64)
          (<= (* (ddr1-ipow 2 o1) y) (- *ddr1-radix* 1))
          (ddr1-normalized-ry-p
           x sz q y msb clz mult o1))))))))

(defun-sk ddr1-unnormalized-branch-p (x sz q y msb)
  (forall (v r i q1 qu rem q2 o5)
    (implies
     (and
      (ddr1-bv64-p v)
      (ddr1-bv64-p r)
      (ddr1-bv32-p i)
      (ddr1-ptr-p q1)
      (ddr1-bv64-p qu)
      (ddr1-bv64-p rem)
      (ddr1-ptr-p q2)
      (ddr1-bv32-p o5))
     (and
      (<= (floor *ddr1-radix* 2) y)
      (implies
       (ddr1-reciprocal-p v y)
       (and
        (<= -1 (ddr1-sint32 msb))
        (<= (ddr1-sint32 msb) (ddr1-sint32 msb))
        (< 0 y)
        (equal
         (ddr1-value-sub
          (ddr1-map-base x)
          (+ (ddr1-offset x) (ddr1-sint32 msb) 1)
          (+ (ddr1-offset x) (ddr1-sint32 sz)))
         (* (ddr1-value-sub
             (ddr1-map-base q)
             (+ (ddr1-offset q) (ddr1-sint32 msb) 1)
             (+ (ddr1-offset q) (ddr1-sint32 sz)))
            y))
        (implies
         (ddr1-same-shape-p q1 q)
         (implies
          (ddr1-unnormalized-loop-invariant-p
           x sz q1 msb i r y)
          (if (<= 0 (ddr1-sint32 i))
              (and
               (ddr1-bounds-at-p x (ddr1-sint32 i))
               (<= (floor *ddr1-radix* 2) y)
               (< r y)
               (ddr1-reciprocal-p v y)
               (implies
                (and
                 (equal
                  (+ (* qu y) rem)
                  (+ (ddr1-map-get
                      (ddr1-map-base x)
                      (+ (ddr1-offset x) (ddr1-sint32 i)))
                     (* *ddr1-radix* r)))
                 (<= 0 rem)
                 (< rem y))
                (let* ((end (+ (ddr1-offset q1)
                                (ddr1-sint32 sz)))
                       (next (+ (ddr1-offset q1)
                                1
                                (ddr1-sint32 i)))
                       (at (+ (ddr1-offset q1)
                              (ddr1-sint32 i)))
                       (base (ddr1-map-base q1)))
                  (and
                   (<= next end)
                   (or (< at next) (<= end at))
                   (implies
                    (equal
                     (ddr1-value-sub base next end)
                     (ddr1-value-sub
                      (ddr1-map-update base at qu)
                      next end))
                    (and
                     (ddr1-bounds-at-p q1 (ddr1-sint32 i))
                     (equal (ddr1-writable q1) t)
                     (implies
                      (ddr1-same-shape-p q2 q1)
                      (implies
                       (and
                        (ddr1-map-equal-p
                         (ddr1-map-base q2)
                         (ddr1-map-update
                          (ddr1-map-base q1)
                          (+ (ddr1-offset q2) (ddr1-sint32 i))
                          qu))
                        (equal
                         (ddr1-map-get
                          (ddr1-map-base q2)
                          (+ (ddr1-offset q2) (ddr1-sint32 i)))
                         qu))
                       (and
                        (ddr1-int32-in-bounds-p
                         (- (ddr1-sint32 i) 1))
                        (implies
                         (equal
                          (ddr1-sint32 o5)
                          (- (ddr1-sint32 i) 1))
                         (and
                          (< (ddr1-sint32 o5) (ddr1-sint32 i))
                          (<= -1 (ddr1-sint32 o5))
                          (<= (ddr1-sint32 o5)
                              (ddr1-sint32 msb))
                          (< rem y)
                          (equal
                           (ddr1-value-sub
                            (ddr1-map-base x)
                            (+ (ddr1-offset x)
                               (ddr1-sint32 o5)
                               1)
                            (+ (ddr1-offset x)
                               (ddr1-sint32 sz)))
                           (+ (* (ddr1-value-sub
                                  (ddr1-map-base q2)
                                  (+ (ddr1-offset q2)
                                     (ddr1-sint32 o5)
                                     1)
                                  (+ (ddr1-offset q2)
                                     (ddr1-sint32 sz)))
                                 y)
                              rem)))))))))))))
            (and
             (equal
              (ddr1-value x (ddr1-sint32 sz))
              (+ (* (ddr1-value q1 (ddr1-sint32 sz)) y) r))
             (< r y)))))))))))

(defun ddr1-clz-premise-p (clz y)
  (let ((clz-i (ddr1-sint32 clz)))
    (and
     (<= (* (ddr1-ipow 2 clz-i) y) (- *ddr1-radix* 1))
     (< (- *ddr1-radix* 1)
        (* 2 (ddr1-ipow 2 clz-i) y))
     (<= 0 clz-i)
     (< clz-i 64))))

(defun-sk ddr1-msb-continuation-p (x sz q y)
  (forall (msb clz)
    (implies
     (and (ddr1-bv32-p msb)
          (ddr1-bv32-p clz))
     (implies
      (equal (ddr1-sint32 msb)
             (- (ddr1-sint32 sz) 1))
      (and
       (< 0 y)
       (implies
        (ddr1-clz-premise-p clz y)
        (if (< 0 (ddr1-sint32 clz))
            (ddr1-normalized-branch-p x sz q y msb clz)
          (ddr1-unnormalized-branch-p x sz q y msb))))))))

(defun-sk
    ntp4vc-pearl-multiprecision-div-div-wmpn-divrem-1qtvc-statement
    ()
  (forall (x sz q y)
    (implies
     (and
      (ddr1-ptr-p x)
      (ddr1-bv32-p sz)
      (ddr1-ptr-p q)
      (ddr1-bv64-p y))
     (implies
      (and
       (ddr1-valid-p x (ddr1-sint32 sz))
       (ddr1-valid-p q (ddr1-sint32 sz))
       (equal (ddr1-writable q) t)
       (< 0 (ddr1-sint32 sz))
       (< 0 y))
      (and
       (ddr1-int32-in-bounds-p (- (ddr1-sint32 sz) 1))
       (ddr1-msb-continuation-p x sz q y))))))

(value-triple :itpeval-statement-checked)
:q
