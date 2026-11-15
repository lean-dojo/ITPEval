;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_free_Why3_ide_VCmemb_free_loop_inv_5_preserved_goal8:
;; the memb loop-invariant consequence that the offset i_1 times the element
;; size equals an earlier indexed offset below i, under the stated pointer,
;; memory, framing, validity, and integer-range hypotheses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mfl5g8-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mfl5g8-address-base (address)
  (car address))

(defun mfl5g8-address-offset (address)
  (cdr address))

(defun mfl5g8-shift (address amount)
  (cons
   (mfl5g8-address-base address)
   (+ (mfl5g8-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_3, integer memories t_1 and t_2, allocation map t, and
;; region function. Linked and sconst are the fixed source predicates applied
;; to the arbitrary functions t and t_2.

(defstub mfl5g8-t3 (address) t)
(defstub mfl5g8-t1 (address) t)
(defstub mfl5g8-allocation (index) t)
(defstub mfl5g8-t2 (address) t)
(defstub mfl5g8-region (base) t)
(defstub mfl5g8-linked-op () t)
(defstub mfl5g8-sconst-op () t)

(defun-sk mfl5g8-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (mfl5g8-address-p address)
      (and
       (mfl5g8-address-p (mfl5g8-t3 address))
       (integerp (mfl5g8-t1 address))
       (integerp (mfl5g8-t2 address))))
     (implies
      (integerp index)
      (integerp (mfl5g8-allocation index)))
     (implies
      (integerp base)
      (integerp (mfl5g8-region base))))))

(defun mfl5g8-linked-p ()
  (if (mfl5g8-linked-op) t nil))

(defun mfl5g8-sconst-p ()
  (if (mfl5g8-sconst-op) t nil))

(defun mfl5g8-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun mfl5g8-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Int.tdiv is truncating integer division. Its zero-divisor value is
;; irrelevant under p_valid_memb, which makes the divisor strictly positive.

(defun mfl5g8-tdiv (numerator denominator)
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

(defun mfl5g8-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mfl5g8-address-base address))
    (<= 0 (mfl5g8-address-offset address))
    (<=
     (+ (mfl5g8-address-offset address) length)
     (mfl5g8-allocation (mfl5g8-address-base address))))))

(defun mfl5g8-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (mfl5g8-address-base address)))
    (<= 0 (mfl5g8-address-offset address))
    (<=
     (+ (mfl5g8-address-offset address) length)
     (mfl5g8-allocation (mfl5g8-address-base address))))))

(defun mfl5g8-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mfl5g8-address-base left)
     (mfl5g8-address-base right)))
   (<=
    (+ (mfl5g8-address-offset right) right-length)
    (mfl5g8-address-offset left))
   (<=
    (+ (mfl5g8-address-offset left) left-length)
    (mfl5g8-address-offset right))))

(defun-sk mfl5g8-framed-p ()
  (forall (address)
    (implies
     (mfl5g8-address-p address)
     (<=
      (mfl5g8-region
       (mfl5g8-address-base (mfl5g8-t3 address)))
      0))))

;; Exact unfoldings of the memb pointer and index functions.

(defun mfl5g8-memb-ptr (m index)
  (mfl5g8-shift
   (mfl5g8-t3 (mfl5g8-shift m 3))
   (* index (mfl5g8-t1 (mfl5g8-shift m 0)))))

(defun mfl5g8-memb-index (m pointer)
  (mfl5g8-tdiv
   (-
    (mfl5g8-address-offset pointer)
    (mfl5g8-address-offset
     (mfl5g8-t3 (mfl5g8-shift m 3))))
   (mfl5g8-t1 (mfl5g8-shift m 0))))

;; Exact unfolding of Axiomatic13.p_valid_memb.

(defun mfl5g8-p-valid-memb-p (m)
  (let*
      ((element-size
        (mfl5g8-t1 (mfl5g8-shift m 0)))
       (element-count
        (mfl5g8-t1 (mfl5g8-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (mfl5g8-t3 (mfl5g8-shift m 2)))
       (payload-array
        (mfl5g8-t3 (mfl5g8-shift m 3)))
       (count-start (mfl5g8-shift count-array 0))
       (payload-start (mfl5g8-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (mfl5g8-valid-rw-p m 4)
     (mfl5g8-valid-rw-p count-array 1)
     (mfl5g8-valid-rw-p payload-array 1)
     (mfl5g8-valid-rw-p count-start element-count)
     (mfl5g8-valid-rw-p payload-start payload-size)
     (mfl5g8-separated-p
      count-start element-count payload-start payload-size))))

;; This is the source universal assertion that every integer index in the
;; earlier prefix has a product different from the scaled offset.

(defun-sk mfl5g8-all-earlier-products-different-p
    (scaled-offset element-size bound)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index bound))
     (not
      (equal
       scaled-offset
       (* index element-size))))))

(defun-sk
    ntp4vc-memb-free-loop-inv-5-preserved-goal8-statement ()
  (forall
   (a i1 i)
   (implies
    (and
     (mfl5g8-function-types-p)
     (mfl5g8-address-p a)
     (integerp i1)
     (integerp i))
    (let*
        ((a1 (mfl5g8-shift a 3))
         (a2 (mfl5g8-t3 a1))
         (a3 (mfl5g8-shift a 0))
         (x (mfl5g8-t1 a3))
         (x1 (* i1 x))
         (a4 (mfl5g8-memb-ptr a i))
         (a5 (mfl5g8-shift a 1))
         (x2 (mfl5g8-t1 a5)))
      (implies
       (and
        (not (equal (mfl5g8-shift a2 x1) a4))
        (equal (mfl5g8-memb-index a a4) i)
        (<= 0 i)
        (<= i1 i)
        (<= 0 i1)
        (< i x2)
        (<= i x2)
        (<= (mfl5g8-region (mfl5g8-address-base a)) 0)
        (<= (mfl5g8-region (mfl5g8-address-base a2)) 0)
        (<= i 2147483646)
        (mfl5g8-framed-p)
        (mfl5g8-linked-p)
        (mfl5g8-sconst-p)
        (mfl5g8-is-sint32-p i)
        (mfl5g8-is-sint32-p i1)
        (mfl5g8-is-uint16-p x2)
        (mfl5g8-is-uint16-p x)
        (mfl5g8-is-sint32-p (+ 1 i))
        (mfl5g8-p-valid-memb-p a)
        (mfl5g8-valid-rd-p a1 1)
        (mfl5g8-valid-rd-p a5 1)
        (mfl5g8-valid-rd-p a3 1))
       (not
        (mfl5g8-all-earlier-products-different-p
         x1 x i)))))))

(value-triple :itpeval-statement-checked)

:q
