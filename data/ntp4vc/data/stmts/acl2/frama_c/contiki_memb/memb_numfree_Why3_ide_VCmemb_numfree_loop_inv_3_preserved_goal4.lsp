;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_numfree_Why3_ide_VCmemb_numfree_loop_inv_3_preserved_goal4:
;; preservation of the zero-slot occurrence count when the memb scan advances
;; by one position, under the stated memory, framing, integer-range, and
;; validity hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mnf4-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mnf4-address-base (address)
  (car address))

(defun mnf4-address-offset (address)
  (cdr address))

(defun mnf4-shift (address amount)
  (cons
   (mnf4-address-base address)
   (+ (mnf4-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_3, integer memories t_1 and t_2, allocation map t, region
;; function, and the linked and sconst predicates at the functions occurring
;; in this verification condition.

(defstub mnf4-t3 (address) t)
(defstub mnf4-t1 (address) t)
(defstub mnf4-t2 (address) t)
(defstub mnf4-allocation (index) t)
(defstub mnf4-region (base) t)
(defstub mnf4-linked-op () t)
(defstub mnf4-sconst-op () t)

(defun-sk mnf4-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (mnf4-address-p address)
      (and
       (mnf4-address-p (mnf4-t3 address))
       (integerp (mnf4-t1 address))
       (integerp (mnf4-t2 address))))
     (implies
      (integerp index)
      (integerp (mnf4-allocation index)))
     (implies
      (integerp base)
      (integerp (mnf4-region base))))))

(defun mnf4-linked-p ()
  (if (mnf4-linked-op) t nil))

(defun mnf4-sconst-p ()
  (if (mnf4-sconst-op) t nil))

(defun mnf4-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun mnf4-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun mnf4-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun mnf4-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mnf4-address-base address))
    (<= 0 (mnf4-address-offset address))
    (<=
     (+ (mnf4-address-offset address) length)
     (mnf4-allocation (mnf4-address-base address))))))

(defun mnf4-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (mnf4-address-base address)))
    (<= 0 (mnf4-address-offset address))
    (<=
     (+ (mnf4-address-offset address) length)
     (mnf4-allocation (mnf4-address-base address))))))

(defun mnf4-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mnf4-address-base left)
     (mnf4-address-base right)))
   (<=
    (+ (mnf4-address-offset right) right-length)
    (mnf4-address-offset left))
   (<=
    (+ (mnf4-address-offset left) left-length)
    (mnf4-address-offset right))))

(defun-sk mnf4-framed-p ()
  (forall (address)
    (implies
     (mnf4-address-p address)
     (<=
      (mnf4-region
       (mnf4-address-base (mnf4-t3 address)))
      0))))

;; Exact unfolding of Axiomatic13.p_valid_memb.

(defun mnf4-p-valid-memb-p (m)
  (let*
      ((element-size
        (mnf4-t1 (mnf4-shift m 0)))
       (element-count
        (mnf4-t1 (mnf4-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (mnf4-t3 (mnf4-shift m 2)))
       (payload-array
        (mnf4-t3 (mnf4-shift m 3)))
       (count-start (mnf4-shift count-array 0))
       (payload-start (mnf4-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (mnf4-valid-rw-p m 4)
     (mnf4-valid-rw-p count-array 1)
     (mnf4-valid-rw-p payload-array 1)
     (mnf4-valid-rw-p count-start element-count)
     (mnf4-valid-rw-p payload-start payload-size)
     (mnf4-separated-p
      count-start element-count payload-start payload-size))))

;; The source occurrence function is uniquely characterized by zero on empty
;; intervals and a one-step recurrence at the right endpoint. This terminating
;; recursion is its exact zero-count instance for t_2.

(defun mnf4-occ-t2-aux (array from remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if
         (equal
          (mnf4-t2
           (mnf4-shift array (+ from (1- remaining))))
          0)
         1
       0)
     (mnf4-occ-t2-aux array from (1- remaining)))))

(defun mnf4-occ-t2 (array from to)
  (if
      (and
       (integerp from)
       (integerp to)
       (< from to))
      (mnf4-occ-t2-aux array from (- to from))
    0))

(defun-sk
    ntp4vc-memb-numfree-loop-inv-3-preserved-goal4-statement ()
  (forall
   (a i2 i i1)
   (implies
    (and
     (mnf4-function-types-p)
     (mnf4-address-p a)
     (integerp i2)
     (integerp i)
     (integerp i1))
    (let*
        ((a1 (mnf4-shift a 1))
         (x (mnf4-t1 a1))
         (a2 (mnf4-shift a 2))
         (a3 (mnf4-t3 a2))
         (x1 (mnf4-occ-t2 a3 0 i2))
         (x2 (+ 1 i2))
         (a4 (mnf4-shift a3 i2))
         (x3 (mnf4-t2 a4)))
      (implies
       (and
        (<= 0 i2)
        (< i2 x)
        (<= i2 x)
        (<= (mnf4-region (mnf4-address-base a)) 0)
        (<= x1 i2)
        (<= i2 2147483646)
        (mnf4-framed-p)
        (mnf4-linked-p)
        (mnf4-sconst-p)
        (mnf4-is-sint32-p i)
        (mnf4-is-sint32-p i1)
        (mnf4-is-sint32-p i2)
        (mnf4-is-uint16-p x)
        (mnf4-is-sint32-p x2)
        (mnf4-p-valid-memb-p a)
        (mnf4-valid-rd-p a2 1)
        (mnf4-valid-rd-p a1 1)
        (mnf4-is-sint8-p x3)
        (mnf4-valid-rd-p a4 1)
        (mnf4-is-sint32-p x1)
        (if (equal x3 0)
            (and
             (equal (+ 1 i) i1)
             (equal x1 i)
             (<= i 2147483646))
          (equal x1 i1)))
       (equal
        (mnf4-occ-t2 a3 0 x2)
        i1))))))

(value-triple :itpeval-statement-checked)

:q
