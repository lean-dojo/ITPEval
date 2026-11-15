;; Statement-only formalization of the ntp4vc corpus artifact
;; pearl/multiprecision/get_str_Get_str_wmpn_limb_get_strqtvc: the loop
;; verification condition for extracting one base digit from a 64-bit limb
;; into a writable byte buffer.  This file contains no proof.

(in-package "ACL2")

(set-ignore-ok t)
(set-irrelevant-formals-ok t)
(set-inhibit-output-lst '(prove proof-tree event summary))

(defun ggl-bv8p (x)
  (and (integerp x) (<= 0 x) (< x 256)))

(defun ggl-bv32p (x)
  (and (integerp x) (<= 0 x) (< x 4294967296)))

(defun ggl-bv64p (x)
  (and (integerp x) (<= 0 x) (< x 18446744073709551616)))

(defun ggl-sint32 (x)
  (if (< x 2147483648) x (- x 4294967296)))

(defun ggl-int32-in-bounds-p (x)
  (and (integerp x) (<= -2147483648 x) (<= x 2147483647)))

(defun ggl-uint64-in-bounds-p (x)
  (and (integerp x) (<= 0 x) (<= x 18446744073709551615)))

(defun ggl-bv8-list-p (xs)
  (if (atom xs)
      (equal xs nil)
    (and (ggl-bv8p (car xs))
         (ggl-bv8-list-p (cdr xs)))))

(defun ggl-ptr8p (p)
  (and (true-listp p)
       (equal (len p) 7)
       (equal (car p) :ptr8)
       (ggl-bv8-list-p (cadr p))
       (integerp (caddr p))
       (integerp (cadddr p))
       (integerp (car (cddddr p)))
       (booleanp (cadr (cddddr p)))))

(defun ggl-data (p)
  (cadr p))

(defun ggl-offset (p)
  (caddr p))

(defun ggl-min (p)
  (cadddr p))

(defun ggl-max (p)
  (car (cddddr p)))

(defun ggl-writable (p)
  (cadr (cddddr p)))

(defun ggl-zone (p)
  (caddr (cddddr p)))

(defun ggl-index (i)
  (if (and (integerp i) (< 0 i)) i 0))

(defun ggl-pelt8 (p i)
  (let ((n (ggl-index i)))
    (if (< n (len (ggl-data p)))
        (nth n (ggl-data p))
      0)))

(defun ggl-valid-p (p size)
  (and (ggl-int32-in-bounds-p size)
       (<= 0 size)
       (<= 0 (ggl-min p))
       (<= (ggl-min p) (ggl-offset p))
       (<= (+ (ggl-offset p) size) (ggl-max p))
       (<= (ggl-max p) (len (ggl-data p)))))

(defun ggl-ptr-bound-p (p i)
  (and (<= (ggl-min p) (+ (ggl-offset p) i))
       (< (+ (ggl-offset p) i) (ggl-max p))))

(defun ggl-ipow (base exponent)
  (expt base (nfix exponent)))

(defun ggl-svalue-le-count (base p start count)
  (if (zp count)
      0
    (+ (ggl-pelt8 p start)
       (* base
          (ggl-svalue-le-count base p (+ start 1) (- count 1))))))

(defun ggl-svalue-le (base p size)
  (ggl-svalue-le-count base p (ggl-offset p) (nfix size)))

(defun-sk ggl-in-base-p (base p n m)
  (forall (k)
    (implies (and (integerp k) (<= n k) (< k m))
             (and (<= 0 (ggl-pelt8 p k))
                  (< (ggl-pelt8 p k) base)))))

(defun ggl-same-meta-p (p q)
  (and (equal (len (ggl-data p)) (len (ggl-data q)))
       (equal (ggl-offset p) (ggl-offset q))
       (equal (ggl-min p) (ggl-min q))
       (equal (ggl-max p) (ggl-max q))
       (equal (ggl-writable p) (ggl-writable q))
       (equal (ggl-zone p) (ggl-zone q))))

(defun-sk ggl-frame-p (new old bound)
  (forall (j)
    (implies (and (integerp j)
                  (or (< j (ggl-offset new))
                      (<= (+ (ggl-offset new) bound) j)))
             (equal (ggl-pelt8 new j)
                    (ggl-pelt8 old j)))))

(defun-sk ggl-single-update-p (new old index byte)
  (forall (j)
    (implies (integerp j)
             (equal (ggl-pelt8 new j)
                    (if (equal j index)
                        byte
                      (ggl-pelt8 old j))))))

(defun ggl-info-b (info)
  (cadr info))

(defun ggl-info-exp (info)
  (caddr info))

(defun ggl-info-bb (info)
  (cadddr info))

(defun ggl-base-infop (info)
  (and (true-listp info)
       (equal (len info) 4)
       (equal (car info) :base-info)
       (integerp (ggl-info-b info))
       (ggl-bv32p (ggl-info-exp info))
       (ggl-bv64p (ggl-info-bb info))
       (<= 2 (ggl-info-b info))
       (<= (ggl-info-b info) 256)
       (< (ggl-info-bb info) 18446744073709551616)
       (<= 18446744073709551616
           (* (ggl-info-bb info) (ggl-info-b info)))
       (<= 7 (ggl-info-exp info))
       (<= (ggl-info-exp info) 63)
       (equal (ggl-info-bb info)
              (ggl-ipow (ggl-info-b info)
                        (ggl-info-exp info)))))

(defun ggl-reciprocal-p (di d1)
  (and (ggl-bv64p di)
       (ggl-bv64p d1)
       (not (equal d1 0))
       (equal di
              (- (floor
                  (- (* 18446744073709551616
                        18446744073709551616)
                     1)
                  d1)
                 18446744073709551616))))

(defun ggl-loop-state-p (base original-sp original-w sz i w1 sp1)
  (and (<= 0 w1)
       (< w1 18446744073709551616)
       (<= 0 (ggl-sint32 i))
       (<= (ggl-sint32 i) (ggl-sint32 sz))
       (implies (< 0 w1)
                (and (<= 0 (ggl-sint32 i))
                     (< (ggl-sint32 i) (ggl-sint32 sz))))
       (ggl-in-base-p
        base sp1
        (ggl-offset sp1)
        (+ (ggl-offset sp1) (ggl-sint32 i)))
       (implies (equal w1 0)
                (implies (< 0 (ggl-sint32 i))
                         (< 0
                            (ggl-pelt8
                             sp1
                             (+ (ggl-offset sp1)
                                (ggl-sint32 i)
                                -1)))))
       (equal original-w
              (+ (ggl-svalue-le base sp1 (ggl-sint32 i))
                 (* (ggl-ipow base (ggl-sint32 i)) w1)))
       (ggl-frame-p sp1 original-sp (ggl-sint32 i))))

(defun ggl-next-loop-state-p
  (base original-sp original-w sz w1 q sp2 o4)
  (and (< q w1)
       (<= 0 q)
       (< q 18446744073709551616)
       (<= 0 (ggl-sint32 o4))
       (<= (ggl-sint32 o4) (ggl-sint32 sz))
       (implies (< 0 q)
                (and (<= 0 (ggl-sint32 o4))
                     (< (ggl-sint32 o4) (ggl-sint32 sz))))
       (ggl-in-base-p
        base sp2
        (ggl-offset sp2)
        (+ (ggl-offset sp2) (ggl-sint32 o4)))
       (implies (equal q 0)
                (implies (< 0 (ggl-sint32 o4))
                         (< 0
                            (ggl-pelt8
                             sp2
                             (+ (ggl-offset sp2)
                                (ggl-sint32 o4)
                                -1)))))
       (equal original-w
              (+ (ggl-svalue-le base sp2 (ggl-sint32 o4))
                 (* (ggl-ipow base (ggl-sint32 o4)) q)))
       (ggl-frame-p sp2 original-sp (ggl-sint32 o4))))

(defun-sk ggl-all-o4-p
  (base original-sp original-w sz i w1 q sp2)
  (forall (o4)
    (implies
     (ggl-bv32p o4)
     (implies
      (equal (ggl-sint32 o4) (+ (ggl-sint32 i) 1))
      (ggl-next-loop-state-p
       base original-sp original-w sz w1 q sp2 o4)))))

(defun-sk ggl-all-sp2-p
  (base original-sp original-w sz i w1 q sp1 o3)
  (forall (sp2)
    (implies
     (ggl-ptr8p sp2)
     (implies
      (ggl-same-meta-p sp2 sp1)
      (implies
       (and
        (ggl-single-update-p
         sp2 sp1
         (+ (ggl-offset sp2) (ggl-sint32 i))
         o3)
        (equal
         (ggl-pelt8 sp2 (+ (ggl-offset sp2) (ggl-sint32 i)))
         o3))
       (and
        (ggl-int32-in-bounds-p (+ (ggl-sint32 i) 1))
        (ggl-all-o4-p
         base original-sp original-w sz i w1 q sp2)))))))

(defun-sk ggl-all-o3-p
  (base original-sp original-w sz i w1 q sp1 o2)
  (forall (o3)
    (implies
     (ggl-bv8p o3)
     (implies
      (equal o3 o2)
      (and
       (ggl-ptr-bound-p sp1 (ggl-sint32 i))
       (equal (ggl-writable sp1) t)
       (ggl-all-sp2-p
        base original-sp original-w sz i w1 q sp1 o3))))))

(defun-sk ggl-all-o2-p
  (base original-sp original-w sz shift i w1 q r sp1)
  (forall (o2)
    (implies
     (ggl-bv64p o2)
     (implies
      (equal r (* (ggl-ipow 2 shift) o2))
      (and
       (<= 0 o2)
       (<= o2 255)
       (ggl-all-o3-p
        base original-sp original-w sz i w1 q sp1 o2))))))

(defun-sk ggl-all-nr-p
  (base original-sp original-w sz shift i w1 q r sp1)
  (forall (nr)
    (implies
     (ggl-bv64p nr)
     (implies
      (equal r (* (ggl-ipow 2 shift) nr))
      (and
       (<= 0 shift)
       (< shift 64)
       (equal (mod r (ggl-ipow 2 shift)) 0)
       (ggl-all-o2-p
        base original-sp original-w sz shift i w1 q r sp1))))))

(defun-sk ggl-all-q-r-p
  (base original-sp original-w sz d1 shift i w1 h l sp1)
  (forall (q r)
    (implies
     (and (ggl-bv64p q) (ggl-bv64p r))
     (implies
      (and
       (equal (+ (* q d1) r)
              (+ l (* 18446744073709551616 h)))
       (<= 0 r)
       (< r d1))
      (and
       (<= 0 shift)
       (< shift 64)
       (equal (mod r (ggl-ipow 2 shift)) 0)
       (ggl-all-nr-p
        base original-sp original-w sz shift i w1 q r sp1))))))

(defun-sk ggl-all-l-p
  (base original-sp original-w sz d1 di shift i w1 h sp1)
  (forall (l)
    (implies
     (ggl-bv64p l)
     (implies
      (equal
       l
       (mod (* w1 (ggl-ipow 2 shift))
            18446744073709551616))
      (and
       (<= 9223372036854775808 d1)
       (< h d1)
       (ggl-reciprocal-p di d1)
       (ggl-all-q-r-p
        base original-sp original-w sz d1 shift i w1 h l sp1))))))

(defun-sk ggl-all-h-p
  (base original-sp original-w sz d1 di shift i w1 o1 sp1)
  (forall (h)
    (implies
     (ggl-bv64p h)
     (implies
      (equal h (floor w1 (ggl-ipow 2 o1)))
      (and
       (<= 0 shift)
       (< shift 64)
       (ggl-all-l-p
        base original-sp original-w sz d1 di shift i w1 h sp1))))))

(defun-sk ggl-all-o1-p
  (base original-sp original-w sz d1 di shift i w1 sp1)
  (forall (o1)
    (implies
     (ggl-bv64p o1)
     (implies
      (equal o1 (- 64 shift))
      (and
       (<= 0 o1)
       (< o1 64)
       (ggl-all-h-p
        base original-sp original-w sz d1 di shift i w1 o1 sp1))))))

(defun ggl-positive-branch-p
  (base original-sp original-w sz d1 di shift i w1 sp1)
  (and
   (ggl-uint64-in-bounds-p (- 64 shift))
   (ggl-all-o1-p
    base original-sp original-w sz d1 di shift i w1 sp1)))

(defun ggl-final-state-p (base original-sp original-w sz sp1 result)
  (and
   (equal (ggl-svalue-le base sp1 result) original-w)
   (<= 0 result)
   (<= result (ggl-sint32 sz))
   (implies
    (< 0 result)
    (< 0
       (ggl-pelt8
        sp1
        (+ (ggl-offset sp1) result -1))))
   (ggl-frame-p sp1 original-sp result)
   (ggl-in-base-p
    base sp1
    (ggl-offset sp1)
    (+ (ggl-offset sp1) result))))

(defun-sk ggl-all-results-p
  (base original-sp original-w sz i sp1)
  (forall (result)
    (implies
     (ggl-bv32p result)
     (implies
      (equal result (ggl-sint32 i))
      (ggl-final-state-p
       base original-sp original-w sz sp1 result)))))

(defun ggl-zero-branch-p
  (base original-sp original-w sz i sp1)
  (and
   (<= 0 (ggl-sint32 i))
   (ggl-all-results-p
    base original-sp original-w sz i sp1)))

(defun ggl-loop-step-p
  (base original-sp original-w sz d1 di shift i w1 sp1)
  (if (< 0 w1)
      (ggl-positive-branch-p
       base original-sp original-w sz d1 di shift i w1 sp1)
    (ggl-zero-branch-p
     base original-sp original-w sz i sp1)))

(defun-sk ggl-all-loop-states-p
  (base original-sp original-w sz d1 di shift)
  (forall (i w1 sp1)
    (implies
     (and
      (ggl-bv32p i)
      (ggl-bv64p w1)
      (ggl-ptr8p sp1))
     (implies
      (ggl-same-meta-p sp1 original-sp)
      (implies
       (ggl-loop-state-p
        base original-sp original-w sz i w1 sp1)
       (ggl-loop-step-p
        base original-sp original-w sz d1 di shift i w1 sp1))))))

(defun ggl-initial-state-p (base sp sz w)
  (and
   (<= 0 w)
   (< w 18446744073709551616)
   (<= 0 0)
   (<= 0 (ggl-sint32 sz))
   (implies (< 0 w)
            (and (<= 0 0)
                 (< 0 (ggl-sint32 sz))))
   (ggl-in-base-p
    base sp (ggl-offset sp) (+ (ggl-offset sp) 0))
   (implies (equal w 0)
            (implies
             (< 0 0)
             (< 0 (ggl-pelt8 sp (+ (ggl-offset sp) 0 -1)))))
   (equal w
          (+ (ggl-svalue-le base sp 0)
             (* (ggl-ipow base 0) w)))))

(defun get-str-get-str-wmpn-limb-get-str-statement
  (binfo sp d1 shift di sz w)
  (let ((base (ggl-info-b binfo)))
    (implies
     (and
      (ggl-base-infop binfo)
      (ggl-ptr8p sp)
      (ggl-bv64p d1)
      (ggl-bv64p shift)
      (ggl-bv64p di)
      (ggl-bv32p sz)
      (ggl-bv64p w)
      (<= 2 base)
      (<= base 256)
      (equal (ggl-writable sp) t)
      (<= 9223372036854775808 d1)
      (<= 0 shift)
      (<= shift 63)
      (equal (* base (ggl-ipow 2 shift)) d1)
      (ggl-reciprocal-p di d1)
      (ggl-valid-p sp (ggl-sint32 sz))
      (< 0 (ggl-sint32 sz))
      (< w (ggl-ipow base (ggl-sint32 sz))))
     (and
      (ggl-initial-state-p base sp sz w)
      (ggl-all-loop-states-p
       base sp w sz d1 di shift)))))

(value-triple :itpeval-statement-checked)
:q
