;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_free_Why3_ide_VCmemb_free_assert_rte_mem_access_4_goal11:
;; readability of the memb count-array pointer field under the stated pointer
;; identity, memory validity, framing, integer-range, and prefix non-aliasing
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mfr11-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mfr11-address-base (address)
  (car address))

(defun mfr11-address-offset (address)
  (cdr address))

(defun mfr11-shift (address amount)
  (cons
   (mfr11-address-base address)
   (+ (mfr11-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_3, integer memories t_1 and t_2, and allocation map t.
;; Region, linked, and sconst are the fixed source operations applied to those
;; arbitrary functions.

(defstub mfr11-t3 (address) t)
(defstub mfr11-t1 (address) t)
(defstub mfr11-allocation (index) t)
(defstub mfr11-t2 (address) t)
(defstub mfr11-region (base) t)
(defstub mfr11-linked-op () t)
(defstub mfr11-sconst-op () t)

(defun-sk mfr11-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (mfr11-address-p address)
      (and
       (mfr11-address-p (mfr11-t3 address))
       (integerp (mfr11-t1 address))
       (integerp (mfr11-t2 address))))
     (implies
      (integerp index)
      (integerp (mfr11-allocation index)))
     (implies
      (integerp base)
      (integerp (mfr11-region base))))))

(defun mfr11-linked-p ()
  (if (mfr11-linked-op) t nil))

(defun mfr11-sconst-p ()
  (if (mfr11-sconst-op) t nil))

(defun mfr11-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun mfr11-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Int.tdiv is truncating integer division. Its zero-divisor value is
;; irrelevant under p_valid_memb, which makes the divisor strictly positive.

(defun mfr11-tdiv (numerator denominator)
  (if
      (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (let ((quotient
             (floor (abs numerator) (abs denominator))))
        (if
            (or
             (and (< numerator 0) (< 0 denominator))
             (and (< 0 numerator) (< denominator 0)))
            (- quotient)
          quotient))
    0))

(defun mfr11-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mfr11-address-base address))
    (<= 0 (mfr11-address-offset address))
    (<=
     (+ (mfr11-address-offset address) length)
     (mfr11-allocation (mfr11-address-base address))))))

(defun mfr11-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (mfr11-address-base address)))
    (<= 0 (mfr11-address-offset address))
    (<=
     (+ (mfr11-address-offset address) length)
     (mfr11-allocation (mfr11-address-base address))))))

(defun mfr11-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mfr11-address-base left)
     (mfr11-address-base right)))
   (<=
    (+ (mfr11-address-offset right) right-length)
    (mfr11-address-offset left))
   (<=
    (+ (mfr11-address-offset left) left-length)
    (mfr11-address-offset right))))

(defun-sk mfr11-framed-p ()
  (forall (address)
    (implies
     (mfr11-address-p address)
     (<=
      (mfr11-region
       (mfr11-address-base (mfr11-t3 address)))
      0))))

;; Exact unfoldings of the memb pointer and index functions.

(defun mfr11-memb-ptr (m index)
  (mfr11-shift
   (mfr11-t3 (mfr11-shift m 3))
   (* index (mfr11-t1 (mfr11-shift m 0)))))

(defun mfr11-memb-index (m pointer)
  (mfr11-tdiv
   (-
    (mfr11-address-offset pointer)
    (mfr11-address-offset
     (mfr11-t3 (mfr11-shift m 3))))
   (mfr11-t1 (mfr11-shift m 0))))

;; This is the exact unfolding of Axiomatic13.p_valid_memb.

(defun mfr11-p-valid-memb-p (m)
  (let*
      ((element-size
        (mfr11-t1 (mfr11-shift m 0)))
       (element-count
        (mfr11-t1 (mfr11-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (mfr11-t3 (mfr11-shift m 2)))
       (payload-array
        (mfr11-t3 (mfr11-shift m 3)))
       (count-start (mfr11-shift count-array 0))
       (payload-start (mfr11-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (mfr11-valid-rw-p m 4)
     (mfr11-valid-rw-p count-array 1)
     (mfr11-valid-rw-p payload-array 1)
     (mfr11-valid-rw-p count-start element-count)
     (mfr11-valid-rw-p payload-start payload-size)
     (mfr11-separated-p
      count-start element-count payload-start payload-size))))

;; The source prefix non-aliasing hypothesis remains universally quantified
;; over every mathematical integer below x.

(defun-sk mfr11-no-earlier-payload-match-p
    (m payload-array bound pointer)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index bound))
     (not
      (equal
       (mfr11-shift
        payload-array
        (* index (mfr11-t1 (mfr11-shift m 0))))
       pointer)))))

(defun-sk
    ntp4vc-memb-free-assert-rte-mem-access-4-goal11-statement ()
  (forall
   (a1 a)
   (implies
    (and
     (mfr11-function-types-p)
     (mfr11-address-p a1)
     (mfr11-address-p a))
    (let*
        ((x (mfr11-memb-index a1 a))
         (a2 (mfr11-shift a1 1))
         (x1 (mfr11-t1 a2))
         (a3 (mfr11-shift a1 3)))
      (implies
       (and
        (equal (mfr11-memb-ptr a1 x) a)
        (<= (mfr11-region (mfr11-address-base a)) 0)
        (<= (mfr11-region (mfr11-address-base a1)) 0)
        (<= 0 x)
        (< x x1)
        (<= x x1)
        (mfr11-framed-p)
        (mfr11-linked-p)
        (mfr11-sconst-p)
        (mfr11-is-uint16-p x1)
        (mfr11-p-valid-memb-p a1)
        (mfr11-valid-rd-p a3 1)
        (mfr11-valid-rd-p a2 1)
        (mfr11-is-sint32-p x)
        (mfr11-no-earlier-payload-match-p
         a1 (mfr11-t3 a3) x a))
       (mfr11-valid-rd-p (mfr11-shift a1 2) 1))))))

(value-triple :itpeval-statement-checked)

:q
