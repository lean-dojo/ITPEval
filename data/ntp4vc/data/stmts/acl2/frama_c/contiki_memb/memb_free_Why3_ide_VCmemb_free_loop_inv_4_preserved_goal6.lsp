;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_free_Why3_ide_VCmemb_free_loop_inv_4_preserved_goal6:
;; preservation of the memb pointer/index round-trip invariant at the
;; successor loop index, under the stated memory, framing, integer-range,
;; validity, and prefix non-aliasing hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mfl4g6-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mfl4g6-address-base (address)
  (car address))

(defun mfl4g6-address-offset (address)
  (cdr address))

(defun mfl4g6-shift (address amount)
  (cons
   (mfl4g6-address-base address)
   (+ (mfl4g6-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_3, integer memories t_1 and t_2, allocation map t, and
;; region function. Linked and sconst are the fixed source predicates applied
;; to the arbitrary functions t and t_2.

(defstub mfl4g6-t3 (address) t)
(defstub mfl4g6-t1 (address) t)
(defstub mfl4g6-allocation (index) t)
(defstub mfl4g6-t2 (address) t)
(defstub mfl4g6-region (base) t)
(defstub mfl4g6-linked-op () t)
(defstub mfl4g6-sconst-op () t)

(defun-sk mfl4g6-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (mfl4g6-address-p address)
      (and
       (mfl4g6-address-p (mfl4g6-t3 address))
       (integerp (mfl4g6-t1 address))
       (integerp (mfl4g6-t2 address))))
     (implies
      (integerp index)
      (integerp (mfl4g6-allocation index)))
     (implies
      (integerp base)
      (integerp (mfl4g6-region base))))))

(defun mfl4g6-linked-p ()
  (if (mfl4g6-linked-op) t nil))

(defun mfl4g6-sconst-p ()
  (if (mfl4g6-sconst-op) t nil))

(defun mfl4g6-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun mfl4g6-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Int.tdiv is truncating integer division. Its zero-divisor value is
;; irrelevant under p_valid_memb, which makes the divisor strictly positive.

(defun mfl4g6-tdiv (numerator denominator)
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

(defun mfl4g6-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mfl4g6-address-base address))
    (<= 0 (mfl4g6-address-offset address))
    (<=
     (+ (mfl4g6-address-offset address) length)
     (mfl4g6-allocation (mfl4g6-address-base address))))))

(defun mfl4g6-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (mfl4g6-address-base address)))
    (<= 0 (mfl4g6-address-offset address))
    (<=
     (+ (mfl4g6-address-offset address) length)
     (mfl4g6-allocation (mfl4g6-address-base address))))))

(defun mfl4g6-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mfl4g6-address-base left)
     (mfl4g6-address-base right)))
   (<=
    (+ (mfl4g6-address-offset right) right-length)
    (mfl4g6-address-offset left))
   (<=
    (+ (mfl4g6-address-offset left) left-length)
    (mfl4g6-address-offset right))))

(defun-sk mfl4g6-framed-p ()
  (forall (address)
    (implies
     (mfl4g6-address-p address)
     (<=
      (mfl4g6-region
       (mfl4g6-address-base (mfl4g6-t3 address)))
      0))))

;; Exact unfoldings of the memb pointer and index functions.

(defun mfl4g6-memb-ptr (m index)
  (mfl4g6-shift
   (mfl4g6-t3 (mfl4g6-shift m 3))
   (* index (mfl4g6-t1 (mfl4g6-shift m 0)))))

(defun mfl4g6-memb-index (m pointer)
  (mfl4g6-tdiv
   (-
    (mfl4g6-address-offset pointer)
    (mfl4g6-address-offset
     (mfl4g6-t3 (mfl4g6-shift m 3))))
   (mfl4g6-t1 (mfl4g6-shift m 0))))

;; Exact unfolding of Axiomatic13.p_valid_memb.

(defun mfl4g6-p-valid-memb-p (m)
  (let*
      ((element-size
        (mfl4g6-t1 (mfl4g6-shift m 0)))
       (element-count
        (mfl4g6-t1 (mfl4g6-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (mfl4g6-t3 (mfl4g6-shift m 2)))
       (payload-array
        (mfl4g6-t3 (mfl4g6-shift m 3)))
       (count-start (mfl4g6-shift count-array 0))
       (payload-start (mfl4g6-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (mfl4g6-valid-rw-p m 4)
     (mfl4g6-valid-rw-p count-array 1)
     (mfl4g6-valid-rw-p payload-array 1)
     (mfl4g6-valid-rw-p count-start element-count)
     (mfl4g6-valid-rw-p payload-start payload-size)
     (mfl4g6-separated-p
      count-start element-count payload-start payload-size))))

;; The source prefix non-aliasing hypothesis remains universally quantified
;; over every mathematical integer strictly below i.

(defun-sk mfl4g6-no-earlier-payload-match-p
    (payload-array element-size bound pointer)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index bound))
     (not
      (equal
       (mfl4g6-shift payload-array (* index element-size))
       pointer)))))

(defun-sk
    ntp4vc-memb-free-loop-inv-4-preserved-goal6-statement ()
  (forall
   (a1 i a)
   (implies
    (and
     (mfl4g6-function-types-p)
     (mfl4g6-address-p a1)
     (integerp i)
     (mfl4g6-address-p a))
    (let*
        ((a2 (mfl4g6-memb-ptr a1 i))
         (a3 (mfl4g6-shift a1 1))
         (x (mfl4g6-t1 a3))
         (a4 (mfl4g6-shift a1 0))
         (x1 (mfl4g6-t1 a4))
         (x2 (+ 1 i))
         (a5 (mfl4g6-shift a1 3)))
      (implies
       (and
        (not (equal a2 a))
        (equal (mfl4g6-memb-index a1 a2) i)
        (<= 0 i)
        (< i x)
        (<= i x)
        (<= (mfl4g6-region (mfl4g6-address-base a)) 0)
        (<= (mfl4g6-region (mfl4g6-address-base a1)) 0)
        (<= i 2147483646)
        (mfl4g6-framed-p)
        (mfl4g6-linked-p)
        (mfl4g6-sconst-p)
        (mfl4g6-is-sint32-p i)
        (mfl4g6-is-uint16-p x)
        (mfl4g6-is-uint16-p x1)
        (mfl4g6-is-sint32-p x2)
        (mfl4g6-p-valid-memb-p a1)
        (mfl4g6-valid-rd-p a5 1)
        (mfl4g6-valid-rd-p a3 1)
        (mfl4g6-valid-rd-p a4 1)
        (mfl4g6-no-earlier-payload-match-p
         (mfl4g6-t3 a5) x1 i a))
       (equal
        x2
        (mfl4g6-memb-index
         a1
         (mfl4g6-memb-ptr a1 x2))))))))

(value-triple :itpeval-statement-checked)

:q
