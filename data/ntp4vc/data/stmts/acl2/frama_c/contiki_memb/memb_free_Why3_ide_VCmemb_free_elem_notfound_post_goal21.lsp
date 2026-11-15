;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_free_Why3_ide_VCmemb_free_elem_notfound_post_goal21:
;; the selected memb count-array cell is zero under the stated pointer/index,
;; non-membership, memory-validity, framing, integer-range, and prefix
;; non-aliasing hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun enp21-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun enp21-address-base (address)
  (car address))

(defun enp21-address-offset (address)
  (cdr address))

(defun enp21-shift (address amount)
  (cons
   (enp21-address-base address)
   (+ (enp21-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_3, integer memories t_1 and t_2, and allocation map t.
;; Region, linked, and sconst are the fixed source operations applied to those
;; arbitrary functions.

(defstub enp21-t3 (address) t)
(defstub enp21-t1 (address) t)
(defstub enp21-t2 (address) t)
(defstub enp21-allocation (index) t)
(defstub enp21-region (base) t)
(defstub enp21-linked-op () t)
(defstub enp21-sconst-op () t)

(defun-sk enp21-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (enp21-address-p address)
      (and
       (enp21-address-p (enp21-t3 address))
       (integerp (enp21-t1 address))
       (integerp (enp21-t2 address))))
     (implies
      (integerp index)
      (integerp (enp21-allocation index)))
     (implies
      (integerp base)
      (integerp (enp21-region base))))))

(defun enp21-linked-p ()
  (if (enp21-linked-op) t nil))

(defun enp21-sconst-p ()
  (if (enp21-sconst-op) t nil))

(defun enp21-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun enp21-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun enp21-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Int.tdiv is truncating integer division. Its zero-divisor value is
;; irrelevant under p_valid_memb, which makes the divisor strictly positive.

(defun enp21-tdiv (numerator denominator)
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

(defun enp21-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (enp21-address-base address))
    (<= 0 (enp21-address-offset address))
    (<=
     (+ (enp21-address-offset address) length)
     (enp21-allocation (enp21-address-base address))))))

(defun enp21-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (enp21-address-base address)))
    (<= 0 (enp21-address-offset address))
    (<=
     (+ (enp21-address-offset address) length)
     (enp21-allocation (enp21-address-base address))))))

(defun enp21-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (enp21-address-base left)
     (enp21-address-base right)))
   (<=
    (+ (enp21-address-offset right) right-length)
    (enp21-address-offset left))
   (<=
    (+ (enp21-address-offset left) left-length)
    (enp21-address-offset right))))

(defun-sk enp21-framed-p ()
  (forall (address)
    (implies
     (enp21-address-p address)
     (<=
      (enp21-region
       (enp21-address-base (enp21-t3 address)))
      0))))

;; Exact unfoldings of the memb pointer and index functions.

(defun enp21-memb-ptr (m index)
  (enp21-shift
   (enp21-t3 (enp21-shift m 3))
   (* index (enp21-t1 (enp21-shift m 0)))))

(defun enp21-memb-index (m pointer)
  (enp21-tdiv
   (-
    (enp21-address-offset pointer)
    (enp21-address-offset
     (enp21-t3 (enp21-shift m 3))))
   (enp21-t1 (enp21-shift m 0))))

;; Exact unfolding of Axiomatic13.p_valid_memb.

(defun enp21-p-valid-memb-p (m)
  (let*
      ((element-size
        (enp21-t1 (enp21-shift m 0)))
       (element-count
        (enp21-t1 (enp21-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (enp21-t3 (enp21-shift m 2)))
       (payload-array
        (enp21-t3 (enp21-shift m 3)))
       (count-start (enp21-shift count-array 0))
       (payload-start (enp21-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (enp21-valid-rw-p m 4)
     (enp21-valid-rw-p count-array 1)
     (enp21-valid-rw-p payload-array 1)
     (enp21-valid-rw-p count-start element-count)
     (enp21-valid-rw-p payload-start payload-size)
     (enp21-separated-p
      count-start element-count payload-start payload-size))))

;; Exact unfolding of p__memb_has, retaining its existential integer index.

(defun-sk enp21-p-memb-has-p (m pointer)
  (exists (index)
    (and
     (integerp index)
     (equal (enp21-memb-ptr m index) pointer)
     (<= 0 index)
     (< index (enp21-t1 (enp21-shift m 1))))))

;; The source prefix non-aliasing hypothesis remains universally quantified
;; over every mathematical integer strictly below i.

(defun-sk enp21-no-earlier-payload-match-p
    (m payload-array bound pointer)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index bound))
     (not
      (equal
       (enp21-shift
        payload-array
        (* index (enp21-t1 (enp21-shift m 0))))
       pointer)))))

(defun-sk ntp4vc-memb-free-elem-notfound-post-goal21-statement ()
  (forall
   (a i)
   (implies
    (and
     (enp21-function-types-p)
     (enp21-address-p a)
     (integerp i))
    (let*
        ((a1 (enp21-memb-ptr a i))
         (a2 (enp21-shift a 1))
         (x (enp21-t1 a2))
         (a3 (enp21-shift a 2))
         (a4 (enp21-shift a 3))
         (a5 (enp21-shift (enp21-t3 a3) i))
         (x1 (enp21-t2 a5)))
      (implies
       (and
        (equal (enp21-memb-index a a1) i)
        (<= 0 i)
        (< i x)
        (<= (enp21-region (enp21-address-base a)) 0)
        (<= (enp21-region (enp21-address-base a1)) 0)
        (enp21-framed-p)
        (enp21-linked-p)
        (enp21-sconst-p)
        (enp21-is-sint32-p i)
        (enp21-is-uint16-p x)
        (enp21-p-valid-memb-p a)
        (enp21-valid-rd-p a3 1)
        (enp21-valid-rd-p a4 1)
        (enp21-valid-rd-p a2 1)
        (enp21-is-sint8-p x1)
        (enp21-valid-rd-p a5 1)
        (enp21-valid-rw-p a5 1)
        (not (enp21-p-memb-has-p a a1))
        (enp21-no-earlier-payload-match-p
         a (enp21-t3 a4) i a1))
       (equal x1 0))))))

(value-triple :itpeval-statement-checked)

:q
