;; Statement-only formalization of the ntp4vc corpus artifact
;; pearl/multiprecision/get_str_Get_str_wmpn_get_str_otherqtvc: the verification
;; condition for converting a positive multiprecision integer to digits in an
;; arbitrary base using normalized-limb division and in-place reversal.  This
;; file contains no proof.

(in-package "ACL2")

(set-ignore-ok t)
(set-irrelevant-formals-ok t)
(set-inhibit-output-lst '(prove proof-tree event summary))

(defun gso-bv8p (x)
  (and (integerp x) (<= 0 x) (< x 256)))

(defun gso-bv32p (x)
  (and (integerp x) (<= 0 x) (< x 4294967296)))

(defun gso-bv64p (x)
  (and (integerp x) (<= 0 x) (< x 18446744073709551616)))

(defun gso-sint32 (x)
  (if (< x 2147483648) x (- x 4294967296)))

(defun gso-int32-in-bounds-p (x)
  (and (integerp x) (<= -2147483648 x) (<= x 2147483647)))

(defun gso-uint32-in-bounds-p (x)
  (and (integerp x) (<= 0 x) (<= x 4294967295)))

(defun gso-bv8-list-p (xs)
  (if (atom xs)
      (equal xs nil)
    (and (gso-bv8p (car xs))
         (gso-bv8-list-p (cdr xs)))))

(defun gso-bv64-list-p (xs)
  (if (atom xs)
      (equal xs nil)
    (and (gso-bv64p (car xs))
         (gso-bv64-list-p (cdr xs)))))

(defun gso-ptr8p (p)
  (and (true-listp p)
       (equal (len p) 7)
       (equal (car p) :ptr8)
       (gso-bv8-list-p (cadr p))
       (integerp (caddr p))
       (integerp (cadddr p))
       (integerp (car (cddddr p)))
       (booleanp (cadr (cddddr p)))))

(defun gso-ptr64p (p)
  (and (true-listp p)
       (equal (len p) 7)
       (equal (car p) :ptr64)
       (gso-bv64-list-p (cadr p))
       (integerp (caddr p))
       (integerp (cadddr p))
       (integerp (car (cddddr p)))
       (booleanp (cadr (cddddr p)))))

(defun gso-data (p) (cadr p))
(defun gso-offset (p) (caddr p))
(defun gso-min (p) (cadddr p))
(defun gso-max (p) (car (cddddr p)))
(defun gso-writable (p) (cadr (cddddr p)))
(defun gso-zone (p) (caddr (cddddr p)))

(defun gso-index (i)
  (if (and (integerp i) (< 0 i)) i 0))

(defun gso-pelt8 (p i)
  (let ((n (gso-index i)))
    (if (< n (len (gso-data p)))
        (nth n (gso-data p))
      0)))

(defun gso-pelt64 (p i)
  (let ((n (gso-index i)))
    (if (< n (len (gso-data p)))
        (nth n (gso-data p))
      0)))

(defun gso-valid-p (p size)
  (and (gso-int32-in-bounds-p size)
       (<= 0 size)
       (<= 0 (gso-min p))
       (<= (gso-min p) (gso-offset p))
       (<= (+ (gso-offset p) size) (gso-max p))
       (<= (gso-max p) (len (gso-data p)))))

(defun gso-ptr-bound-p (p i)
  (and (<= (gso-min p) (+ (gso-offset p) i))
       (< (+ (gso-offset p) i) (gso-max p))))

(defun gso-ipow (base exponent)
  (expt base (nfix exponent)))

(defun gso-value-count (p start count)
  (if (zp count)
      0
    (+ (gso-pelt64 p start)
       (* 18446744073709551616
          (gso-value-count p (+ 1 start) (- count 1))))))

(defun gso-value (p size)
  (gso-value-count p (gso-offset p) (nfix size)))

(defun gso-svalue-le-count (base p start count)
  (if (zp count)
      0
    (+ (gso-pelt8 p start)
       (* base
          (gso-svalue-le-count base p (+ 1 start) (- count 1))))))

(defun gso-svalue-le-sub (base p n m)
  (gso-svalue-le-count base p n (nfix (- m n))))

(defun gso-svalue-le (base p size)
  (gso-svalue-le-sub base p (gso-offset p) (+ (gso-offset p) size)))

(defun gso-svalue-sub-count (base p start count)
  (if (zp count)
      0
    (+ (gso-pelt8 p (+ start (- count 1)))
       (* base
          (gso-svalue-sub-count base p start (- count 1))))))

(defun gso-svalue-sub (base p n m)
  (gso-svalue-sub-count base p n (nfix (- m n))))

(defun gso-svalue (base p size)
  (gso-svalue-sub base p (gso-offset p) (+ (gso-offset p) size)))

(defun gso-info-b (info) (cadr info))
(defun gso-info-exp (info) (caddr info))
(defun gso-info-bb (info) (cadddr info))

(defun gso-infop (info)
  (and (true-listp info)
       (equal (len info) 4)
       (equal (car info) :base-info)
       (integerp (gso-info-b info))
       (gso-bv32p (gso-info-exp info))
       (gso-bv64p (gso-info-bb info))
       (<= 2 (gso-info-b info))
       (<= (gso-info-b info) 256)
       (< (gso-info-bb info) 18446744073709551616)
       (<= 18446744073709551616
           (* (gso-info-bb info) (gso-info-b info)))
       (<= 7 (gso-info-exp info))
       (<= (gso-info-exp info) 63)
       (equal (gso-info-bb info)
              (gso-ipow (gso-info-b info) (gso-info-exp info)))))

(defun gso-reciprocal-p (di d1)
  (and (gso-bv64p di)
       (gso-bv64p d1)
       (not (equal d1 0))
       (equal di
              (- (floor (- (* 18446744073709551616
                              18446744073709551616)
                           1)
                        d1)
                 18446744073709551616))))

(defun gso-same-meta-p (p q)
  (and (equal (len (gso-data p)) (len (gso-data q)))
       (equal (gso-offset p) (gso-offset q))
       (equal (gso-min p) (gso-min q))
       (equal (gso-max p) (gso-max q))
       (equal (gso-writable p) (gso-writable q))
       (equal (gso-zone p) (gso-zone q))))

(defun gso-shifted-ptr8-p (spn sp1 sn)
  (and (equal (gso-offset spn) (+ (gso-offset sp1) sn))
       (equal (len (gso-data spn)) (len (gso-data sp1)))
       (equal (gso-data spn) (gso-data sp1))
       (equal (gso-min spn) (gso-min sp1))
       (equal (gso-max spn) (gso-max sp1))
       (equal (gso-zone spn) (gso-zone sp1))
       (equal (gso-writable spn) (gso-writable sp1))))

(defun-sk gso-in-base-p (base p n m)
  (forall (k)
    (implies (and (integerp k) (<= n k) (< k m))
             (and (<= 0 (gso-pelt8 p k))
                  (< (gso-pelt8 p k) base)))))

(defun-sk gso-frame8-p (new old bound)
  (forall (k)
    (implies (and (integerp k)
                  (or (< k (gso-offset new))
                      (<= (+ (gso-offset new) bound) k)))
             (equal (gso-pelt8 new k) (gso-pelt8 old k)))))

(defun-sk gso-frame64-p (new old bound)
  (forall (k)
    (implies (and (integerp k)
                  (or (< k (gso-offset new))
                      (<= (+ (gso-offset new) bound) k)))
             (equal (gso-pelt64 new k) (gso-pelt64 old k)))))

(defun-sk gso-map-eq-sub-shift-p (x y xi yi size)
  (forall (i)
    (implies (and (integerp i) (<= 0 i) (< i size))
             (equal (gso-pelt64 x (+ xi i))
                    (gso-pelt64 y (+ yi i))))))

(defun-sk gso-single-update8-p (new old index byte)
  (forall (k)
    (implies (integerp k)
             (equal (gso-pelt8 new k)
                    (if (equal k index)
                        byte
                      (gso-pelt8 old k))))))

(defun-sk gso-middle-unchanged-p (new old lo hi)
  (forall (j)
    (implies (and (integerp j) (<= lo j) (< j hi))
             (equal (gso-pelt8 new j) (gso-pelt8 old j)))))

(defun gso-limb-post-p (base out limit input)
  (and (equal (gso-svalue-le base out limit) input)
       (<= 0 limit)
       (implies (< 0 limit)
                (< 0
                   (gso-pelt8 out
                              (+ (gso-offset out) limit -1))))
       (gso-in-base-p base out
                      (gso-offset out)
                      (+ (gso-offset out) limit))))

(defun gso-reverse-invariant-p (base sp sz sp2 o8 i sp3)
  (and (<= 0 (+ (* 2 (gso-sint32 i)) 1))
       (<= (+ (* 2 (gso-sint32 i)) 1)
           (+ (gso-sint32 o8) 1))
       (gso-middle-unchanged-p
        sp3 sp2
        (+ (gso-offset sp3) (gso-sint32 i))
        (+ (gso-offset sp3) (gso-sint32 o8) (- (gso-sint32 i))))
       (gso-in-base-p base sp3
                      (gso-offset sp3)
                      (+ (gso-offset sp3) (gso-sint32 o8)))
       (equal
        (gso-svalue-sub base sp3
                        (gso-offset sp3)
                        (+ (gso-offset sp3) (gso-sint32 i)))
        (gso-svalue-le-sub
         base sp2
         (+ (gso-offset sp3) (gso-sint32 o8) (- (gso-sint32 i)))
         (+ (gso-offset sp3) (gso-sint32 o8))))
       (equal
        (gso-svalue-sub
         base sp3
         (+ (gso-offset sp3) (gso-sint32 o8) (- (gso-sint32 i)))
         (+ (gso-offset sp3) (gso-sint32 o8)))
        (gso-svalue-le-sub base sp2
                           (gso-offset sp3)
                           (+ (gso-offset sp3) (gso-sint32 i))))
       (equal
        (gso-svalue-le-sub
         base sp3
         (+ (gso-offset sp3) (gso-sint32 i))
         (+ (gso-offset sp3) (gso-sint32 o8) (- (gso-sint32 i))))
        (gso-svalue-le-sub
         base sp2
         (+ (gso-offset sp3) (gso-sint32 i))
         (+ (gso-offset sp3) (gso-sint32 o8) (- (gso-sint32 i)))))
       (implies (< 0 (gso-sint32 i))
                (< 0 (gso-pelt8 sp3 (gso-offset sp3))))
       (gso-frame8-p sp3 sp sz)))

(defun-sk gso-final-result-p (up un base sp sz sp3 o8)
  (forall (result)
    (implies (and (gso-bv32p result)
                  (equal result (gso-sint32 o8)))
             (and (<= 0 result)
                  (< result (gso-sint32 sz))
                  (equal (gso-svalue base sp3 result)
                         (gso-value up (gso-sint32 un)))
                  (gso-in-base-p base sp3
                                 (gso-offset sp3)
                                 (+ (gso-offset sp3) result))
                  (< 0 (gso-pelt8 sp3 (gso-offset sp3)))
                  (gso-frame8-p sp3 sp (gso-sint32 sz))))))

(defun gso-reverse-next-invariant-p
  (base sp sz sp2 o8 i sp5 o16)
  (and (<= 0 (- (gso-sint32 o8) (gso-sint32 i)))
       (< (- (gso-sint32 o8) (gso-sint32 o16))
          (- (gso-sint32 o8) (gso-sint32 i)))
       (gso-reverse-invariant-p base sp sz sp2 o8 o16 sp5)))

(defun-sk gso-second-swap-next-p
  (base sp sz sp2 o8 i sp5)
  (forall (o16)
    (implies
     (and (gso-bv32p o16)
          (equal (gso-sint32 o16) (+ (gso-sint32 i) 1)))
     (gso-reverse-next-invariant-p
      base sp sz sp2 o8 i sp5 o16))))

(defun-sk gso-second-swap-write-p
  (base sp sz sp2 o8 i sp4 temp-byte o15)
  (forall (sp5)
    (implies
     (and
      (gso-ptr8p sp5)
      (gso-same-meta-p sp5 sp4)
      (gso-single-update8-p
       sp5 sp4
       (+ (gso-offset sp5) (gso-sint32 o15))
       temp-byte)
      (equal (gso-pelt8 sp5
                        (+ (gso-offset sp5) (gso-sint32 o15)))
             temp-byte))
     (and
      (gso-int32-in-bounds-p (+ (gso-sint32 i) 1))
      (gso-second-swap-next-p base sp sz sp2 o8 i sp5)))))

(defun-sk gso-second-swap-index-p
  (base sp sz sp2 o8 i sp4 temp-byte o14)
  (forall (o15)
    (implies
     (and
      (gso-bv32p o15)
      (equal (gso-sint32 o15) (- (gso-sint32 o14) 1)))
     (and
      (gso-ptr-bound-p sp4 (gso-sint32 o15))
      (equal (gso-writable sp4) t)
      (gso-second-swap-write-p
       base sp sz sp2 o8 i sp4 temp-byte o15)))))

(defun-sk gso-second-swap-p
  (base sp sz sp2 o8 i sp4 temp-byte)
  (forall (o14)
    (implies
     (and
      (gso-bv32p o14)
      (equal (gso-sint32 o14)
             (- (gso-sint32 o8) (gso-sint32 i))))
     (and
      (gso-int32-in-bounds-p (- (gso-sint32 o14) 1))
      (gso-second-swap-index-p
       base sp sz sp2 o8 i sp4 temp-byte o14)))))

(defun-sk gso-first-swap-p
  (base sp sz sp2 o8 i sp3 temp-byte o12 o13)
  (forall (sp4)
    (implies
     (and (gso-ptr8p sp4)
          (gso-same-meta-p sp4 sp3)
          (gso-single-update8-p
           sp4 sp3
           (+ (gso-offset sp4) (gso-sint32 i))
           o13)
          (equal (gso-pelt8 sp4
                            (+ (gso-offset sp4) (gso-sint32 i)))
                 o13))
     (and
      (gso-int32-in-bounds-p
       (- (gso-sint32 o8) (gso-sint32 i)))
      (gso-second-swap-p
       base sp sz sp2 o8 i sp4 temp-byte)))))

(defun-sk gso-reverse-index-p
  (base sp sz sp2 o8 i sp3 o11)
  (forall (o12)
    (implies
     (and (gso-bv32p o12)
          (equal (gso-sint32 o12) (- (gso-sint32 o11) 1)))
     (and
      (gso-ptr-bound-p sp3 (gso-sint32 o12))
      (let ((temp-byte (gso-pelt8 sp3
                                  (+ (gso-offset sp3) (gso-sint32 i))))
            (o13 (gso-pelt8 sp3
                            (+ (gso-offset sp3) (gso-sint32 o12)))))
        (and
         (gso-ptr-bound-p sp3 (gso-sint32 i))
         (equal (gso-writable sp3) t)
         (gso-first-swap-p
          base sp sz sp2 o8 i sp3 temp-byte o12 o13)))))))

(defun-sk gso-reverse-continue-p
  (base sp sz sp2 o8 i sp3)
  (forall (o11)
    (implies
     (and (gso-bv32p o11)
          (equal (gso-sint32 o11)
                 (- (gso-sint32 o8) (gso-sint32 i))))
     (and
      (gso-int32-in-bounds-p (- (gso-sint32 o11) 1))
      (gso-reverse-index-p base sp sz sp2 o8 i sp3 o11)))))

(defun-sk gso-reverse-test-p
  (up un base sp sz sp2 o8 i sp3 o9)
  (forall (o10)
    (implies
     (and (gso-bv32p o10)
          (equal (gso-sint32 o10) (+ (gso-sint32 o9) 1)))
     (if (< (gso-sint32 o10) (gso-sint32 o8))
         (and
          (gso-ptr-bound-p sp3 (gso-sint32 i))
          (gso-int32-in-bounds-p
           (- (gso-sint32 o8) (gso-sint32 i)))
          (gso-reverse-continue-p base sp sz sp2 o8 i sp3))
       (and
        (<= 0 (gso-sint32 o8))
        (gso-final-result-p up un base sp sz sp3 o8))))))

(defun-sk gso-reverse-step-p
  (up un base sp sz sp2 o8 i sp3)
  (forall (o9)
    (implies
     (and (gso-bv32p o9)
          (equal (gso-sint32 o9) (* 2 (gso-sint32 i))))
     (and
      (gso-int32-in-bounds-p (+ (gso-sint32 o9) 1))
      (gso-reverse-test-p up un base sp sz sp2 o8 i sp3 o9)))))

(defun-sk gso-reverse-loop-p
  (up un base sp sz sp2 o8)
  (forall (i sp3)
    (implies
     (and (gso-bv32p i)
          (gso-ptr8p sp3)
          (gso-same-meta-p sp3 sp2)
          (gso-reverse-invariant-p base sp sz sp2 o8 i sp3))
     (and
      (gso-int32-in-bounds-p (* 2 (gso-sint32 i)))
      (gso-reverse-step-p up un base sp sz sp2 o8 i sp3)))))

(defun gso-reverse-initial-p (base sp sz sp2 o8)
  (and (<= 1 (+ (gso-sint32 o8) 1))
       (gso-in-base-p base sp2
                      (gso-offset sp2)
                      (+ (gso-offset sp2) (gso-sint32 o8)))
       (equal
        (gso-svalue-sub base sp2 (gso-offset sp2) (gso-offset sp2))
        (gso-svalue-le-sub
         base sp2
         (+ (gso-offset sp2) (gso-sint32 o8))
         (+ (gso-offset sp2) (gso-sint32 o8))))
       (equal
        (gso-svalue-sub
         base sp2
         (+ (gso-offset sp2) (gso-sint32 o8))
         (+ (gso-offset sp2) (gso-sint32 o8)))
        (gso-svalue-le-sub base sp2
                           (gso-offset sp2)
                           (gso-offset sp2)))
       (gso-frame8-p sp2 sp sz)))

(defun-sk gso-after-final-sum-p
  (up un base sp sz sn sp2 o7)
  (forall (o8)
    (implies
     (and (gso-bv32p o8)
          (equal (gso-sint32 o8)
                 (+ (gso-sint32 sn) (gso-sint32 o7))))
     (and
      (gso-reverse-initial-p base sp (gso-sint32 sz) sp2 o8)
      (gso-reverse-loop-p up un base sp sz sp2 o8)))))

(defun-sk gso-after-final-limb-p
  (up un base sp sz sn sp2 sdone)
  (forall (o7)
    (implies
     (and (gso-bv32p o7)
          (equal (gso-sint32 o7) sdone))
     (and
      (gso-int32-in-bounds-p
       (+ (gso-sint32 sn) (gso-sint32 o7)))
      (gso-after-final-sum-p
       up un base sp sz sn sp2 o7)))))

(defun-sk gso-final-limb-output-p
  (up un info base sp sz sn spn spn1 sp2 o4 o6)
  (forall (sdone)
    (implies
     (and (gso-bv32p sdone)
          (gso-limb-post-p
           (gso-info-b info) spn1 sdone o4)
          (<= sdone (gso-sint32 o6))
          (gso-frame8-p spn1 spn sdone))
     (and
      (<= sdone 2147483647)
      (gso-after-final-limb-p up un base sp sz sn sp2 sdone)))))

(defun-sk gso-final-alias-p
  (up un info base sp sz sn sp1 spn o4 o6)
  (forall (spn1 sp2)
    (implies
     (and (gso-ptr8p spn1)
          (gso-ptr8p sp2)
          (equal (gso-data spn1) (gso-data sp2))
          (equal (len (gso-data sp2)) (len (gso-data spn)))
          (equal (gso-offset spn1) (gso-offset spn))
          (equal (gso-min spn1) (gso-min spn))
          (equal (gso-max spn1) (gso-max spn))
          (equal (gso-writable spn1) (gso-writable spn))
          (equal (gso-zone spn1) (gso-zone spn))
          (gso-same-meta-p sp2 sp1))
     (gso-final-limb-output-p
      up un info base sp sz sn spn spn1 sp2 o4 o6))))

(defun gso-limb-call-pre-p
  (info shift d1 di spn size input)
  (and (<= 2 (gso-info-b info))
       (<= (gso-info-b info) 256)
       (equal (gso-writable spn) t)
       (<= 9223372036854775808 d1)
       (<= 0 shift)
       (<= shift 63)
       (equal (* (gso-info-b info) (gso-ipow 2 shift)) d1)
       (gso-reciprocal-p di d1)
       (gso-valid-p spn size)
       (< 0 size)
       (< input (gso-ipow (gso-info-b info) size))))

(defun-sk gso-final-size-p
  (up un info base sp sz sn sp1 spn shift d1 di o4 o5)
  (forall (o6)
    (implies
     (and (gso-bv32p o6)
          (equal (gso-sint32 o6)
                 (- (gso-sint32 o5) (gso-sint32 sn))))
     (and
      (gso-limb-call-pre-p
       info shift d1 di spn (gso-sint32 o6) o4)
      (gso-final-alias-p
       up un info base sp sz sn sp1 spn o4 o6)))))

(defun-sk gso-final-capacity-p
  (up un info base sp sz sn sp1 spn shift d1 di o4)
  (forall (o5)
    (implies
     (and (gso-bv32p o5)
          (equal (gso-sint32 o5) (- (gso-sint32 sz) 1)))
     (and
      (gso-int32-in-bounds-p
       (- (gso-sint32 o5) (gso-sint32 sn)))
      (gso-final-size-p
       up un info base sp sz sn sp1 spn shift d1 di o4 o5)))))

(defun-sk gso-final-shifted-p
  (up un info base sp sz sn sp1 shift d1 di o4)
  (forall (spn)
    (implies
     (and (gso-ptr8p spn)
          (gso-shifted-ptr8-p spn sp1 (gso-sint32 sn)))
     (and
      (gso-int32-in-bounds-p (- (gso-sint32 sz) 1))
      (gso-final-capacity-p
       up un info base sp sz sn sp1 spn shift d1 di o4)))))

(defun gso-final-state-body-p
  (up un info base sp sz sn up1 sp1 shift d1 di)
  (let ((o4 (gso-pelt64 up1 (gso-offset up1))))
    (and
     (gso-ptr-bound-p up1 0)
     (<= (gso-min sp1) (+ (gso-offset sp1) (gso-sint32 sn)))
     (<= (+ (gso-offset sp1) (gso-sint32 sn)) (gso-max sp1))
     (gso-final-shifted-p
      up un info base sp sz sn sp1 shift d1 di o4))))

(defun-sk gso-final-continuation-p
  (up un info base sp sz shift d1 di vu)
  (forall (sn up1 sp1)
    (implies
     (and (gso-bv32p sn)
          (gso-ptr64p up1)
          (gso-ptr8p sp1)
          (gso-same-meta-p up1 up)
          (gso-same-meta-p sp1 sp)
          (equal
           (+ (gso-svalue-le base sp1 (gso-sint32 sn))
              (* (gso-ipow base (gso-sint32 sn))
                 (gso-value up1 1)))
           vu)
          (gso-in-base-p base sp1
                         (gso-offset sp1)
                         (+ (gso-offset sp1) (gso-sint32 sn)))
          (<= 0 (gso-sint32 sn))
          (< (gso-sint32 sn) (gso-sint32 sz))
          (< 0 (gso-value up1 1))
          (gso-frame8-p sp1 sp (gso-sint32 sz)))
     (gso-final-state-body-p
      up un info base sp sz sn up1 sp1 shift d1 di))))

(defun gso-outer-state-p
  (up un info base sp sz vu loopi n sn up1 sp1)
  (and
   (equal
    (+ (gso-svalue-le base sp1 (gso-sint32 sn))
       (* (gso-ipow base (gso-sint32 sn))
          (gso-value up1 (gso-sint32 n))))
    vu)
   (<= 1 (gso-sint32 n))
   (<= (gso-sint32 n) (gso-sint32 un))
   (<= (- (gso-sint32 un) (gso-sint32 n)) loopi)
   (<= 0 (gso-sint32 sn))
   (< (gso-sint32 sn) (gso-sint32 sz))
   (equal (gso-sint32 sn) (* loopi (gso-info-exp info)))
   (gso-in-base-p base sp1
                  (gso-offset sp1)
                  (+ (gso-offset sp1) (gso-sint32 sn)))
   (< 0
      (gso-pelt64
       up1
       (+ (gso-offset up1) (gso-sint32 n) -1)))
   (gso-frame8-p sp1 sp (gso-sint32 sz))))

(defun gso-outer-terminal-p
  (base sp sz vu sn up1 sp1)
  (and
   (equal
    (+ (gso-svalue-le base sp1 (gso-sint32 sn))
       (* (gso-ipow base (gso-sint32 sn))
          (gso-value up1 1)))
    vu)
   (gso-in-base-p base sp1
                  (gso-offset sp1)
                  (+ (gso-offset sp1) (gso-sint32 sn)))
   (<= 0 (gso-sint32 sn))
   (< (gso-sint32 sn) (gso-sint32 sz))
   (< 0 (gso-value up1 1))
   (gso-frame8-p sp1 sp (gso-sint32 sz))))

(defun gso-padding-state-p
  (info base sp sz vu sn up2 o11 sdone sn1 sp3)
  (and
   (<= sdone (gso-info-exp info))
   (equal (gso-sint32 sn1) (+ (gso-sint32 sn) sdone))
   (gso-in-base-p base sp3
                  (gso-offset sp3)
                  (+ (gso-offset sp3) (gso-sint32 sn1)))
   (equal
    (+ (gso-svalue-le base sp3 (gso-sint32 sn1))
       (* (gso-ipow
           base
           (+ (- (gso-sint32 sn1) sdone)
              (gso-info-exp info)))
          (gso-value up2 (gso-sint32 o11))))
    vu)
   (gso-frame8-p sp3 sp (gso-sint32 sz))))

(defun gso-after-digit-state-p
  (info base sp sz vu sn up2 o11 digit-count o17 sp2)
  (and
   (<= digit-count (gso-info-exp info))
   (equal (gso-sint32 o17) (+ (gso-sint32 sn) digit-count))
   (gso-in-base-p base sp2
                  (gso-offset sp2)
                  (+ (gso-offset sp2) (gso-sint32 o17)))
   (equal
    (+ (gso-svalue-le base sp2 (gso-sint32 o17))
       (* (gso-ipow
           base
           (+ (- (gso-sint32 o17) digit-count)
              (gso-info-exp info)))
          (gso-value up2 (gso-sint32 o11))))
    vu)
   (gso-frame8-p sp2 sp (gso-sint32 sz))))

(defun-sk gso-padding-next-count-p
  (up un info base sp sz vu loopi n sn up1 up2 o11
      sdone sp4 o18)
  (forall (o19)
    (implies
     (and
      (gso-bv32p o19)
      (equal o19 (+ sdone 1)))
     (and
      (<= 0 (- (gso-info-exp info) sdone))
      (< (- (gso-info-exp info) o19)
         (- (gso-info-exp info) sdone))
      (gso-padding-state-p
       info base sp sz vu sn up2 o11 o19 o18 sp4)))))

(defun-sk gso-padding-next-size-p
  (up un info base sp sz vu loopi n sn up1 up2 o11
      sdone sn1 sp4)
  (forall (o18)
    (implies
     (and
      (gso-bv32p o18)
      (equal (gso-sint32 o18) (+ (gso-sint32 sn1) 1)))
     (and
      (gso-uint32-in-bounds-p (+ sdone 1))
      (gso-padding-next-count-p
       up un info base sp sz vu loopi n sn up1 up2 o11
       sdone sp4 o18)))))

(defun-sk gso-padding-write-p
  (up un info base sp sz vu loopi n sn up1 up2 o11
      sdone sn1 sp3)
  (forall (sp4)
    (implies
     (and
      (gso-ptr8p sp4)
      (gso-same-meta-p sp4 sp3)
      (gso-single-update8-p
       sp4 sp3
       (+ (gso-offset sp4) (gso-sint32 sn1))
       0)
      (equal (gso-pelt8 sp4
                        (+ (gso-offset sp4) (gso-sint32 sn1)))
             0))
     (and
      (gso-int32-in-bounds-p (+ (gso-sint32 sn1) 1))
      (gso-padding-next-size-p
       up un info base sp sz vu loopi n sn up1 up2 o11
       sdone sn1 sp4)))))

(defun gso-padding-exit-p
  (up un info base sp sz vu loopi n sn up1 up2 o11 sn1 sp3)
  (and
   (<= 0 (gso-value up1 (gso-sint32 n)))
   (< (gso-value up2 (gso-sint32 o11))
      (gso-value up1 (gso-sint32 n)))
   (gso-outer-state-p
    up un info base sp sz vu (+ loopi 1)
    o11 sn1 up2 sp3)))

(defun gso-padding-step-p
  (up un info base sp sz vu loopi n sn up1 up2 o11
      sdone sn1 sp3)
  (if (< sdone (gso-info-exp info))
      (and
       (gso-ptr-bound-p sp3 (gso-sint32 sn1))
       (equal (gso-writable sp3) t)
       (gso-padding-write-p
        up un info base sp sz vu loopi n sn up1 up2 o11
        sdone sn1 sp3))
    (gso-padding-exit-p
     up un info base sp sz vu loopi n sn up1 up2 o11 sn1 sp3)))

(defun-sk gso-padding-loop-p
  (up un info base sp sz vu loopi n sn up1 up2 o11 sp2)
  (forall (sdone sn1 sp3)
    (implies
     (and (gso-bv32p sdone)
          (gso-bv32p sn1)
          (gso-ptr8p sp3)
          (gso-same-meta-p sp3 sp2)
          (gso-padding-state-p
           info base sp sz vu sn up2 o11 sdone sn1 sp3))
     (gso-padding-step-p
      up un info base sp sz vu loopi n sn up1 up2 o11
      sdone sn1 sp3))))

(defun-sk gso-after-limb-sum-p
  (up un info base sp sz vu loopi n sn up1 up2 o11
      sp2 digit-count o16)
  (forall (o17)
    (implies
     (and (gso-bv32p o17)
          (equal (gso-sint32 o17)
                 (+ (gso-sint32 sn) (gso-sint32 o16))))
     (and
      (gso-after-digit-state-p
       info base sp sz vu sn up2 o11 digit-count o17 sp2)
      (gso-padding-loop-p
       up un info base sp sz vu loopi n sn up1 up2 o11 sp2)))))

(defun-sk gso-after-limb-count-p
  (up un info base sp sz vu loopi n sn up1 up2 o11
      sp2 digit-count)
  (forall (o16)
    (implies
     (and (gso-bv32p o16)
          (equal (gso-sint32 o16) digit-count))
     (and
      (gso-int32-in-bounds-p
       (+ (gso-sint32 sn) (gso-sint32 o16)))
      (gso-after-limb-sum-p
       up un info base sp sz vu loopi n sn up1 up2 o11
       sp2 digit-count o16)))))

(defun-sk gso-inner-limb-output-p
  (up un info base sp sz vu loopi n sn up1 up2 o11
      spn spn1 sp2 remainder o14)
  (forall (o15)
    (implies
     (and (gso-bv32p o15)
          (gso-limb-post-p
           (gso-info-b info) spn1 o15 remainder)
          (<= o15 (gso-sint32 o14))
          (gso-frame8-p spn1 spn o15))
     (and
      (<= o15 2147483647)
      (gso-after-limb-count-p
       up un info base sp sz vu loopi n sn up1 up2 o11
       sp2 o15)))))

(defun-sk gso-inner-alias-p
  (up un info base sp sz vu loopi n sn up1 up2 o11
      sp1 spn remainder o14)
  (forall (spn1 sp2)
    (implies
     (and
      (gso-ptr8p spn1)
      (gso-ptr8p sp2)
      (equal (gso-data spn1) (gso-data sp2))
      (equal (len (gso-data sp2)) (len (gso-data spn)))
      (equal (gso-offset spn1) (gso-offset spn))
      (equal (gso-min spn1) (gso-min spn))
      (equal (gso-max spn1) (gso-max spn))
      (equal (gso-writable spn1) (gso-writable spn))
      (equal (gso-zone spn1) (gso-zone spn))
      (gso-same-meta-p sp2 sp1))
     (gso-inner-limb-output-p
      up un info base sp sz vu loopi n sn up1 up2 o11
      spn spn1 sp2 remainder o14))))

(defun-sk gso-inner-limb-size-p
  (up un info base sp sz vu loopi n sn up1 up2 o11
      sp1 spn shift d1 di remainder o13)
  (forall (o14)
    (implies
     (and (gso-bv32p o14)
          (equal (gso-sint32 o14) (+ (gso-sint32 o13) 1)))
     (and
      (gso-limb-call-pre-p
       info shift d1 di spn (gso-sint32 o14) remainder)
      (gso-inner-alias-p
       up un info base sp sz vu loopi n sn up1 up2 o11
       sp1 spn remainder o14)))))

(defun-sk gso-inner-exp-p
  (up un info base sp sz vu loopi n sn up1 up2 o11
      sp1 spn shift d1 di remainder)
  (forall (o13)
    (implies
     (and (gso-bv32p o13)
          (equal (gso-sint32 o13) (gso-info-exp info)))
     (and
      (gso-int32-in-bounds-p (+ (gso-sint32 o13) 1))
      (gso-inner-limb-size-p
       up un info base sp sz vu loopi n sn up1 up2 o11
       sp1 spn shift d1 di remainder o13)))))

(defun-sk gso-inner-shifted-p
  (up un info base sp sz vu loopi n sn up1 up2 o11
      sp1 shift d1 di remainder)
  (forall (spn)
    (implies
     (and (gso-ptr8p spn)
          (gso-shifted-ptr8-p spn sp1 (gso-sint32 sn)))
     (and
      (<= (gso-info-exp info) 2147483647)
      (gso-inner-exp-p
       up un info base sp sz vu loopi n sn up1 up2 o11
       sp1 spn shift d1 di remainder)))))

(defun gso-after-new-size-p
  (up un info base sp sz vu loopi n sn up1 up2 o11
      sp1 shift d1 di remainder)
  (and
   (<= (gso-min sp1) (+ (gso-offset sp1) (gso-sint32 sn)))
   (<= (+ (gso-offset sp1) (gso-sint32 sn)) (gso-max sp1))
   (gso-inner-shifted-p
    up un info base sp sz vu loopi n sn up1 up2 o11
    sp1 shift d1 di remainder)))

(defun-sk gso-new-size-p
  (up un info base sp sz vu loopi n sn up1 up2
      sp1 shift d1 di remainder o10)
  (forall (o11)
    (implies
     (and (gso-bv32p o11)
          (equal (gso-sint32 o11)
                 (- (gso-sint32 n) (gso-sint32 o10))))
     (gso-after-new-size-p
      up un info base sp sz vu loopi n sn up1 up2 o11
      sp1 shift d1 di remainder))))

(defun-sk gso-leading-zero-choice-p
  (up un info base sp sz vu loopi n sn up1 up2
      sp1 shift d1 di remainder o8 o9)
  (forall (o10)
    (implies
     (and (gso-bv32p o10)
          (equal o10 (if o9 1 0)))
     (and
      (gso-int32-in-bounds-p
       (- (gso-sint32 n) (gso-sint32 o10)))
      (gso-new-size-p
       up un info base sp sz vu loopi n sn up1 up2
       sp1 shift d1 di remainder o10)))))

(defun-sk gso-leading-zero-p
  (up un info base sp sz vu loopi n sn up1 up2
      sp1 shift d1 di remainder o8)
  (forall (o9)
    (implies
     (and
      (booleanp o9)
      (implies (equal o8 0) (equal o9 t))
      (implies (equal o9 t) (equal o8 0)))
     (gso-leading-zero-choice-p
      up un info base sp sz vu loopi n sn up1 up2
      sp1 shift d1 di remainder o8 o9))))

(defun-sk gso-last-limb-index-p
  (up un info base sp sz vu loopi n sn up1 up2
      sp1 shift d1 di remainder)
  (forall (o7)
    (implies
     (and (gso-bv32p o7)
          (equal (gso-sint32 o7) (- (gso-sint32 n) 1)))
     (and
      (gso-ptr-bound-p up2 (gso-sint32 o7))
      (let ((o8 (gso-pelt64
                 up2
                 (+ (gso-offset up2) (gso-sint32 o7)))))
        (gso-leading-zero-p
         up un info base sp sz vu loopi n sn up1 up2
         sp1 shift d1 di remainder o8))))))

(defun-sk gso-copy-quotient-p
  (up un info base sp sz vu loopi n sn up1 tp2
      sp1 shift d1 di remainder)
  (forall (up2)
    (implies
     (and
      (gso-ptr64p up2)
      (gso-same-meta-p up2 up1)
      (gso-map-eq-sub-shift-p
       up2 tp2 (gso-offset up2) (gso-offset tp2) (gso-sint32 n))
      (gso-frame64-p up2 up1 (gso-sint32 n)))
     (and
      (gso-int32-in-bounds-p (- (gso-sint32 n) 1))
      (gso-last-limb-index-p
       up un info base sp sz vu loopi n sn up1 up2
       sp1 shift d1 di remainder)))))

(defun-sk gso-division-output-p
  (up un info base sp sz vu loopi n sn up1 tp2
      sp1 shift d1 di)
  (forall (remainder)
    (implies
     (and
      (gso-bv64p remainder)
      (equal
       (gso-value up1 (gso-sint32 n))
       (+ (* (gso-value tp2 (gso-sint32 n))
             (gso-info-bb info))
          remainder))
      (< remainder (gso-info-bb info)))
     (and
      (gso-valid-p tp2 (gso-sint32 n))
      (gso-valid-p up1 (gso-sint32 n))
      (equal (gso-writable up1) t)
      (gso-copy-quotient-p
       up un info base sp sz vu loopi n sn up1 tp2
       sp1 shift d1 di remainder)))))

(defun-sk gso-division-buffer-p
  (up un info base sp sz vu loopi n sn up1 tp1
      sp1 shift d1 di)
  (forall (tp2)
    (implies
     (and (gso-ptr64p tp2)
          (gso-same-meta-p tp2 tp1))
     (gso-division-output-p
      up un info base sp sz vu loopi n sn up1 tp2
      sp1 shift d1 di))))

(defun gso-outer-continue-p
  (up un info base sp sz vu loopi tp1 n sn up1 sp1 shift d1 di)
  (and
   (gso-valid-p up1 (gso-sint32 n))
   (gso-valid-p tp1 (gso-sint32 n))
   (equal (gso-writable tp1) t)
   (< 0 (gso-sint32 n))
   (< 0 (gso-info-bb info))
   (gso-division-buffer-p
    up un info base sp sz vu loopi n sn up1 tp1
    sp1 shift d1 di)))

(defun gso-outer-step-p
  (up un info base sp sz vu loopi tp1 n sn up1 sp1 shift d1 di)
  (if (< 1 (gso-sint32 n))
      (gso-outer-continue-p
       up un info base sp sz vu loopi tp1 n sn up1 sp1 shift d1 di)
    (gso-outer-terminal-p base sp sz vu sn up1 sp1)))

(defun-sk gso-outer-loop-p
  (up un info base sp sz vu tp shift d1 di)
  (forall (loopi tp1 n sn up1 sp1)
    (implies
     (and
      (integerp loopi)
      (gso-ptr64p tp1)
      (gso-bv32p n)
      (gso-bv32p sn)
      (gso-ptr64p up1)
      (gso-ptr8p sp1)
      (gso-same-meta-p tp1 tp)
      (gso-same-meta-p up1 up)
      (gso-same-meta-p sp1 sp)
      (gso-outer-state-p
       up un info base sp sz vu loopi n sn up1 sp1))
     (gso-outer-step-p
      up un info base sp sz vu loopi tp1 n sn up1 sp1
      shift d1 di))))

(defun gso-initial-outer-state-p
  (up un info base sp sz vu)
  (and
   (equal
    (+ (gso-svalue-le base sp 0)
       (* (gso-ipow base 0)
          (gso-value up (gso-sint32 un))))
    vu)
   (<= 1 (gso-sint32 un))
   (<= (gso-sint32 un) (gso-sint32 un))
   (<= (- (gso-sint32 un) (gso-sint32 un)) 0)
   (<= 0 0)
   (< 0 (gso-sint32 sz))
   (equal 0 (* 0 (gso-info-exp info)))
   (gso-in-base-p base sp (gso-offset sp) (gso-offset sp))
   (< 0
      (gso-pelt64
       up
       (+ (gso-offset up) (gso-sint32 un) -1)))))

(defun-sk gso-initial-temp-p
  (up un info base sp sz shift d1 di vu o4)
  (forall (tp)
    (implies
     (and
      (gso-ptr64p tp)
      (equal (len (gso-data tp)) o4)
      (equal (gso-offset tp) 0)
      (equal (gso-min tp) 0)
      (equal (gso-max tp) o4)
      (equal (gso-writable tp) t))
     (and
      (gso-initial-outer-state-p up un info base sp sz vu)
      (gso-outer-loop-p
       up un info base sp sz vu tp shift d1 di)))))

(defun-sk gso-multi-branch-p
  (up un info base sp sz shift d1 di vu)
  (forall (o4)
    (implies
     (and (gso-bv32p o4)
          (equal o4 (gso-sint32 un)))
     (and
      (<= 0 o4)
      (gso-initial-temp-p
       up un info base sp sz shift d1 di vu o4)))))

(defun gso-single-branch-p (up base sp sz vu)
  (and
   (equal
    (+ (gso-svalue-le base sp 0)
       (* (gso-ipow base 0) (gso-value up 1)))
    vu)
   (gso-in-base-p base sp (gso-offset sp) (gso-offset sp))
   (<= 0 0)
   (< 0 (gso-sint32 sz))
   (< 0 (gso-value up 1))))

(defun gso-program-body-p
  (up un info base sp sz shift d1 di)
  (let ((vu (gso-value up (gso-sint32 un))))
    (and
     (if (< 1 (gso-sint32 un))
         (and
          (<= 0 (gso-sint32 un))
          (gso-multi-branch-p
           up un info base sp sz shift d1 di vu))
       (gso-single-branch-p up base sp sz vu))
     (gso-final-continuation-p
      up un info base sp sz shift d1 di vu))))

(defun-sk gso-reciprocal-continuation-p
  (up un info base sp sz shift d1)
  (forall (di)
    (implies
     (and (gso-bv64p di)
          (gso-reciprocal-p di d1))
     (gso-program-body-p
      up un info base sp sz shift d1 di))))

(defun-sk gso-normalized-divisor-p
  (up un info base sp sz shift o3)
  (forall (d1)
    (implies
     (and
      (gso-bv64p d1)
      (equal d1 (* (gso-ipow 2 shift) o3)))
     (and
      (<= 9223372036854775808 d1)
      (gso-reciprocal-continuation-p
       up un info base sp sz shift d1)))))

(defun-sk gso-base-word-p
  (up un info base sp sz shift)
  (forall (o3)
    (implies
     (and (gso-bv64p o3)
          (equal o3 (gso-sint32 base)))
     (and
      (<= 0 shift)
      (< shift 64)
      (<= (* (gso-ipow 2 shift) o3) 18446744073709551615)
      (gso-normalized-divisor-p
       up un info base sp sz shift o3)))))

(defun-sk gso-shift-word-p
  (up un info base sp sz o2)
  (forall (shift)
    (implies
     (and (gso-bv64p shift)
          (equal shift (gso-sint32 o2)))
     (and
      (<= 0 (gso-sint32 base))
      (gso-base-word-p up un info base sp sz shift)))))

(defun-sk gso-normalization-shift-p
  (up un info base sp sz o1)
  (forall (o2)
    (implies
     (and
      (gso-bv32p o2)
      (<= (* (gso-ipow 2 (gso-sint32 o2)) o1)
          18446744073709551615)
      (< 18446744073709551615
         (* 2 (gso-ipow 2 (gso-sint32 o2)) o1))
      (<= 0 (gso-sint32 o2))
      (< (gso-sint32 o2) 64))
     (and
      (<= 0 (gso-sint32 o2))
      (gso-shift-word-p up un info base sp sz o2)))))

(defun-sk gso-base-cast-p (up un info base sp sz)
  (forall (o1)
    (implies
     (and (gso-bv64p o1)
          (equal o1 (gso-sint32 base)))
     (and
      (< 0 o1)
      (gso-normalization-shift-p
       up un info base sp sz o1)))))

(defun gso-hypotheses-p (up un info base sp sz)
  (and
   (gso-ptr64p up)
   (gso-bv32p un)
   (gso-infop info)
   (gso-bv32p base)
   (gso-ptr8p sp)
   (gso-bv32p sz)
   (gso-valid-p up (gso-sint32 un))
   (<= 1 (gso-sint32 un))
   (equal (gso-info-b info) (gso-sint32 base))
   (equal (gso-writable up) t)
   (equal (gso-writable sp) t)
   (< 0
      (gso-pelt64
       up
       (+ (gso-offset up) (gso-sint32 un) -1)))
   (< 0 (gso-sint32 sz))
   (gso-valid-p sp (gso-sint32 sz))
   (< (gso-value up (gso-sint32 un))
      (gso-ipow (gso-sint32 base) (- (gso-sint32 sz) 1)))))

(defun gso-wmpn-get-str-other-statement
  (up un info base sp sz)
  (implies
   (gso-hypotheses-p up un info base sp sz)
   (and
    (<= 0 (gso-sint32 base))
    (gso-base-cast-p up un info base sp sz))))

(value-triple :itpeval-statement-checked)
:q
