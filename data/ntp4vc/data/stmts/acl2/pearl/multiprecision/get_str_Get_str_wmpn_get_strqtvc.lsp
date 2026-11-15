;; Statement-only formalization of the ntp4vc corpus artifact
;; pearl/multiprecision/get_str_Get_str_wmpn_get_strqtvc: the call-site
;; verification condition for converting a positive multiprecision integer
;; into base digits through the power-of-two or general-base branch.  This file
;; contains no proof.

(in-package "ACL2")

(defun gstr-bv8p (x)
  (and (integerp x) (<= 0 x) (< x 256)))

(defun gstr-bv32p (x)
  (and (integerp x) (<= 0 x) (< x 4294967296)))

(defun gstr-bv64p (x)
  (and (integerp x) (<= 0 x) (< x 18446744073709551616)))

(defun gstr-sint32 (x)
  (if (< x 2147483648) x (- x 4294967296)))

(defun gstr-uint32 (x)
  x)

(defun gstr-bv32-zero ()
  0)

(defun gstr-int32-in-bounds-p (x)
  (and (integerp x) (<= -2147483648 x) (<= x 2147483647)))

(defun gstr-bv8-list-p (xs)
  (if (atom xs)
      (equal xs nil)
    (and (gstr-bv8p (car xs))
         (gstr-bv8-list-p (cdr xs)))))

(defun gstr-bv64-list-p (xs)
  (if (atom xs)
      (equal xs nil)
    (and (gstr-bv64p (car xs))
         (gstr-bv64-list-p (cdr xs)))))

(defun gstr-ptr8p (p)
  (and (true-listp p)
       (equal (len p) 7)
       (equal (car p) :ptr8)
       (gstr-bv8-list-p (cadr p))
       (integerp (caddr p))
       (integerp (cadddr p))
       (integerp (car (cddddr p)))
       (booleanp (cadr (cddddr p)))))

(defun gstr-ptr64p (p)
  (and (true-listp p)
       (equal (len p) 7)
       (equal (car p) :ptr64)
       (gstr-bv64-list-p (cadr p))
       (integerp (caddr p))
       (integerp (cadddr p))
       (integerp (car (cddddr p)))
       (booleanp (cadr (cddddr p)))))

(defun gstr-data (p)
  (cadr p))

(defun gstr-offset (p)
  (caddr p))

(defun gstr-min (p)
  (cadddr p))

(defun gstr-max (p)
  (car (cddddr p)))

(defun gstr-writable (p)
  (cadr (cddddr p)))

(defun gstr-zone (p)
  (caddr (cddddr p)))

(defun gstr-index (i)
  (if (and (integerp i) (< 0 i)) i 0))

(defun gstr-pelt8 (p i)
  (let ((n (gstr-index i)))
    (if (< n (len (gstr-data p)))
        (nth n (gstr-data p))
      0)))

(defun gstr-pelt64 (p i)
  (let ((n (gstr-index i)))
    (if (< n (len (gstr-data p)))
        (nth n (gstr-data p))
      0)))

(defun gstr-valid-p (p size)
  (and (gstr-int32-in-bounds-p size)
       (<= 0 size)
       (<= 0 (gstr-min p))
       (<= (gstr-min p) (gstr-offset p))
       (<= (+ (gstr-offset p) size) (gstr-max p))
       (<= (gstr-max p) (len (gstr-data p)))))

(defun gstr-ipow (base exponent)
  (expt base (nfix exponent)))

(defun gstr-ediv (x y)
  (if (and (integerp x) (integerp y) (not (equal y 0)))
      (floor x y)
    0))

(defun gstr-value-count (p start count)
  (if (zp count)
      0
    (+ (gstr-pelt64 p start)
       (* 18446744073709551616
          (gstr-value-count p (+ 1 start) (- count 1))))))

(defun gstr-value (p size)
  (gstr-value-count p (gstr-offset p) (nfix size)))

(defun gstr-svalue-count (base p start count)
  (if (zp count)
      0
    (+ (gstr-pelt8 p (+ start (- count 1)))
       (* base
          (gstr-svalue-count base p start (- count 1))))))

(defun gstr-svalue (base p size)
  (gstr-svalue-count base p (gstr-offset p) (nfix size)))

(defun-sk gstr-in-base-p (base p n m)
  (forall (k)
    (implies (and (integerp k) (<= n k) (< k m))
             (and (<= 0 (gstr-pelt8 p k))
                  (< (gstr-pelt8 p k) base)))))

(defun gstr-same-meta-p (p q)
  (and (equal (len (gstr-data p)) (len (gstr-data q)))
       (equal (gstr-offset p) (gstr-offset q))
       (equal (gstr-min p) (gstr-min q))
       (equal (gstr-max p) (gstr-max q))
       (equal (gstr-writable p) (gstr-writable q))
       (equal (gstr-zone p) (gstr-zone q))))

(defun-sk gstr-frame-p (new old bound)
  (forall (k)
    (implies (and (integerp k)
                  (or (< k (gstr-offset new))
                      (<= (+ (gstr-offset new) bound) k)))
             (equal (gstr-pelt8 new k)
                    (gstr-pelt8 old k)))))

(defun gstr-info-b (info)
  (cadr info))

(defun gstr-info-exp (info)
  (caddr info))

(defun gstr-info-bb (info)
  (cadddr info))

(defun gstr-base-infop (info)
  (and (true-listp info)
       (equal (len info) 4)
       (equal (car info) :base-info)
       (integerp (gstr-info-b info))
       (gstr-bv32p (gstr-info-exp info))
       (gstr-bv64p (gstr-info-bb info))
       (<= 2 (gstr-info-b info))
       (<= (gstr-info-b info) 256)
       (< (gstr-info-bb info) 18446744073709551616)
       (<= 18446744073709551616
           (* (gstr-info-bb info) (gstr-info-b info)))
       (<= 7 (gstr-info-exp info))
       (<= (gstr-info-exp info) 63)
       (equal (gstr-info-bb info)
              (gstr-ipow (gstr-info-b info)
                         (gstr-info-exp info)))))

(defun gstr-final-postcondition-p (base up un sp1 sz result)
  (and (gstr-in-base-p
        (gstr-sint32 base)
        sp1
        (gstr-offset sp1)
        (+ (gstr-offset sp1) result))
       (equal (gstr-svalue (gstr-sint32 base) sp1 result)
              (gstr-value up (gstr-sint32 un)))
       (< 0 result)
       (< result (gstr-sint32 sz))
       (< 0 (gstr-pelt8 sp1 (gstr-offset sp1)))))

(defun gstr-bits-result-premise-p (up un sp bits o2 sp1 result)
  (let ((digit-base (gstr-ipow 2 bits))
        (allocation
         (gstr-ediv (+ (gstr-sint32 o2) bits -1) bits)))
    (and (gstr-in-base-p
          digit-base
          sp1
          (gstr-offset sp1)
          (+ (gstr-offset sp1) result))
         (equal (gstr-svalue digit-base sp1 result)
                (gstr-value up (gstr-sint32 un)))
         (< 0 result)
         (<= result allocation)
         (< 0 (gstr-pelt8 sp1 (gstr-offset sp1)))
         (gstr-frame-p sp1 sp allocation))))

(defun-sk gstr-bits-all-results-p (base up un sp sz bits o2 sp1)
  (forall (result)
    (implies
     (gstr-bv32p result)
     (implies
      (gstr-bits-result-premise-p up un sp bits o2 sp1 result)
      (gstr-final-postcondition-p base up un sp1 sz result)))))

(defun-sk gstr-bits-all-sp1-p (base up un sp sz bits o2)
  (forall (sp1)
    (implies
     (gstr-ptr8p sp1)
     (implies
      (gstr-same-meta-p sp1 sp)
      (gstr-bits-all-results-p base up un sp sz bits o2 sp1)))))

(defun gstr-bits-call-p (base up un sp sz bits o2)
  (let ((allocation
         (gstr-ediv (+ (gstr-sint32 o2) bits -1) bits)))
    (and (<= 1 (gstr-sint32 un))
         (gstr-valid-p up (gstr-sint32 un))
         (<= 1 bits)
         (<= bits 8)
         (gstr-valid-p sp allocation)
         (<= 0 (gstr-sint32 o2))
         (< (gstr-value up (gstr-sint32 un))
            (gstr-ipow 2 (gstr-sint32 o2)))
         (< 0 (gstr-pelt64
               up
               (+ (gstr-offset up) (gstr-sint32 un) -1)))
         (<= (+ (* 64 (gstr-sint32 un)) 7) 2147483647)
         (equal (gstr-writable sp) t)
         (gstr-bits-all-sp1-p base up un sp sz bits o2))))

(defun-sk gstr-bits-all-o2-p (base up un sp sz bits)
  (forall (o2)
    (implies
     (gstr-bv32p o2)
     (implies
      (equal (gstr-sint32 o2) (* 64 (gstr-sint32 un)))
      (gstr-bits-call-p base up un sp sz bits o2)))))

(defun gstr-power-of-two-branch-p (base up un sp sz bits)
  (and (gstr-int32-in-bounds-p (* 64 (gstr-sint32 un)))
       (gstr-bits-all-o2-p base up un sp sz bits)))

(defun gstr-other-result-premise-p (base up un sp sz sp1 result)
  (and (<= 0 result)
       (< result (gstr-sint32 sz))
       (equal (gstr-svalue (gstr-sint32 base) sp1 result)
              (gstr-value up (gstr-sint32 un)))
       (gstr-in-base-p
        (gstr-sint32 base)
        sp1
        (gstr-offset sp1)
        (+ (gstr-offset sp1) result))
       (< 0 (gstr-pelt8 sp1 (gstr-offset sp1)))
       (gstr-frame-p sp1 sp (gstr-sint32 sz))))

(defun-sk gstr-other-all-results-p (base up un sp sz sp1)
  (forall (result)
    (implies
     (gstr-bv32p result)
     (implies
      (gstr-other-result-premise-p base up un sp sz sp1 result)
      (gstr-final-postcondition-p base up un sp1 sz result)))))

(defun-sk gstr-other-all-sp1-p (base up un sp sz)
  (forall (sp1)
    (implies
     (gstr-ptr8p sp1)
     (implies
      (gstr-same-meta-p sp1 sp)
      (gstr-other-all-results-p base up un sp sz sp1)))))

(defun gstr-other-call-p (base up un sp sz info)
  (and (gstr-valid-p up (gstr-sint32 un))
       (<= 1 (gstr-sint32 un))
       (equal (gstr-info-b info) (gstr-sint32 base))
       (equal (gstr-writable up) t)
       (< 0 (gstr-pelt64
             up
             (+ (gstr-offset up) (gstr-sint32 un) -1)))
       (equal (gstr-writable sp) t)
       (< 0 (gstr-sint32 sz))
       (gstr-valid-p sp (gstr-sint32 sz))
       (< (gstr-value up (gstr-sint32 un))
          (gstr-ipow (gstr-sint32 base)
                     (- (gstr-sint32 sz) 1)))
       (gstr-other-all-sp1-p base up un sp sz)))

(defun-sk gstr-other-all-info-p (base up un sp sz o2)
  (forall (info)
    (implies
     (gstr-base-infop info)
     (implies
      (equal (gstr-info-b info) o2)
      (gstr-other-call-p base up un sp sz info)))))

(defun-sk gstr-other-all-o2-p (base up un sp sz)
  (forall (o2)
    (implies
     (gstr-bv64p o2)
     (implies
      (equal o2 (gstr-sint32 base))
      (and (<= 2 o2)
           (<= o2 256)
           (gstr-other-all-info-p base up un sp sz o2))))))

(defun gstr-general-base-branch-p (base up un sp sz)
  (and (<= 0 (gstr-sint32 base))
       (gstr-other-all-o2-p base up un sp sz)))

(defun-sk gstr-not-a-power-of-two-p (o1)
  (forall (n)
    (implies
     (and (integerp n) (<= 0 n))
     (not (equal (gstr-ipow 2 n) o1)))))

(defun gstr-bits-contract-p (o1 bits)
  (and (<= 0 bits)
       (<= bits 8)
       (implies (not (equal bits 0))
                (equal (gstr-ipow 2 bits) o1))
       (implies (equal bits 0)
                (gstr-not-a-power-of-two-p o1))))

(defun-sk gstr-all-bits-p (base up un sp sz o1)
  (forall (bits)
    (implies
     (gstr-bv32p bits)
     (implies
      (gstr-bits-contract-p o1 bits)
      (implies
       (implies (equal (gstr-uint32 bits) 0)
                (equal bits (gstr-bv32-zero)))
       (if (not (equal bits (gstr-bv32-zero)))
           (gstr-power-of-two-branch-p base up un sp sz bits)
         (gstr-general-base-branch-p base up un sp sz)))))))

(defun-sk gstr-all-o1-p (base up un sp sz)
  (forall (o1)
    (implies
     (gstr-bv64p o1)
     (implies
      (equal o1 (gstr-sint32 base))
      (and (<= 2 o1)
           (<= o1 256)
           (gstr-all-bits-p base up un sp sz o1))))))

(defun get-str-get-str-wmpn-get-str-statement
  (sz un sp up base)
  (implies
   (and (gstr-bv32p sz)
        (gstr-bv32p un)
        (gstr-ptr8p sp)
        (gstr-ptr64p up)
        (gstr-bv32p base)
        (< 0 (gstr-sint32 sz))
        (< 0 (gstr-sint32 un))
        (gstr-valid-p sp (gstr-sint32 sz))
        (gstr-valid-p up (gstr-sint32 un))
        (equal (gstr-writable sp) t)
        (equal (gstr-writable up) t)
        (<= (gstr-ipow 18446744073709551616
                       (gstr-sint32 un))
            (gstr-ipow (gstr-sint32 base)
                       (- (gstr-sint32 sz) 1)))
        (< 0 (gstr-pelt64
              up
              (+ (gstr-offset up) (gstr-sint32 un) -1)))
        (<= 2 (gstr-sint32 base))
        (<= (gstr-sint32 base) 256)
        (<= (+ (* 64 (gstr-sint32 un)) 7) 2147483647))
   (and (<= 0 (gstr-sint32 base))
        (gstr-all-o1-p base up un sp sz))))

(value-triple :itpeval-statement-checked)
:q
