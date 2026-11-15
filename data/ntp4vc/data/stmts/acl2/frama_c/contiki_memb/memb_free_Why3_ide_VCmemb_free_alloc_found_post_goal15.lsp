;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_free_Why3_ide_VCmemb_free_alloc_found_post_goal15:
;; freeing the selected allocated memb slot makes that pointer unallocated
;; under the stated memory, framing, integer-range, validity, update, and
;; prior-payload-alias hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mf15-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mf15-address-base (address)
  (car address))

(defun mf15-address-offset (address)
  (cdr address))

(defun mf15-shift (address amount)
  (cons
   (mf15-address-base address)
   (+ (mf15-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_2, pointer memory t_5, allocation maps t and t_1, and
;; integer memories t_4 and t_3. Region, linked, and sconst are the fixed
;; source operations applied to those arbitrary functions.

(defstub mf15-t2 (address) t)
(defstub mf15-t5 (address) t)
(defstub mf15-t (index) t)
(defstub mf15-t4 (address) t)
(defstub mf15-t1 (index) t)
(defstub mf15-t3 (address) t)
(defstub mf15-region (base) t)
(defstub mf15-linked-op () t)
(defstub mf15-sconst-op () t)

(defun-sk mf15-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (mf15-address-p address)
      (and
       (integerp (mf15-t2 address))
       (mf15-address-p (mf15-t5 address))
       (integerp (mf15-t4 address))
       (integerp (mf15-t3 address))))
     (implies
      (integerp index)
      (and
       (integerp (mf15-t index))
       (integerp (mf15-t1 index))))
     (implies
      (integerp base)
      (integerp (mf15-region base))))))

(defun mf15-linked-p ()
  (if (mf15-linked-op) t nil))

(defun mf15-sconst-p ()
  (if (mf15-sconst-op) t nil))

(defun mf15-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun mf15-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Int.tdiv is truncating integer division. Its zero-divisor value is
;; irrelevant under p_valid_memb, which makes the divisor strictly positive.

(defun mf15-tdiv (numerator denominator)
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

(defun mf15-valid-rw-t-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mf15-address-base address))
    (<= 0 (mf15-address-offset address))
    (<=
     (+ (mf15-address-offset address) length)
     (mf15-t (mf15-address-base address))))))

(defun mf15-valid-rd-t-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (mf15-address-base address)))
    (<= 0 (mf15-address-offset address))
    (<=
     (+ (mf15-address-offset address) length)
     (mf15-t (mf15-address-base address))))))

(defun mf15-valid-rw-t1-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mf15-address-base address))
    (<= 0 (mf15-address-offset address))
    (<=
     (+ (mf15-address-offset address) length)
     (mf15-t1 (mf15-address-base address))))))

(defun mf15-valid-rd-t1-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (mf15-address-base address)))
    (<= 0 (mf15-address-offset address))
    (<=
     (+ (mf15-address-offset address) length)
     (mf15-t1 (mf15-address-base address))))))

(defun mf15-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mf15-address-base left)
     (mf15-address-base right)))
   (<=
    (+ (mf15-address-offset right) right-length)
    (mf15-address-offset left))
   (<=
    (+ (mf15-address-offset left) left-length)
    (mf15-address-offset right))))

(defun-sk mf15-framed-p ()
  (forall (address)
    (implies
     (mf15-address-p address)
     (<=
      (mf15-region
       (mf15-address-base (mf15-t5 address)))
      0))))

;; Exact unfoldings of the memb pointer and index functions.

(defun mf15-memb-ptr (m index)
  (mf15-shift
   (mf15-t5 (mf15-shift m 3))
   (* index (mf15-t2 (mf15-shift m 0)))))

(defun mf15-memb-index (m pointer)
  (mf15-tdiv
   (-
    (mf15-address-offset pointer)
    (mf15-address-offset
     (mf15-t5 (mf15-shift m 3))))
   (mf15-t2 (mf15-shift m 0))))

;; This is the exact unfolding of Axiomatic13.p_valid_memb.

(defun mf15-p-valid-memb-p (m)
  (let*
      ((element-size
        (mf15-t2 (mf15-shift m 0)))
       (element-count
        (mf15-t2 (mf15-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (mf15-t5 (mf15-shift m 2)))
       (payload-array
        (mf15-t5 (mf15-shift m 3)))
       (count-start (mf15-shift count-array 0))
       (payload-start (mf15-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (mf15-valid-rw-t-p m 4)
     (mf15-valid-rw-t-p count-array 1)
     (mf15-valid-rw-t-p payload-array 1)
     (mf15-valid-rw-t-p count-start element-count)
     (mf15-valid-rw-t-p payload-start payload-size)
     (mf15-separated-p
      count-start element-count payload-start payload-size))))

;; Exact unfolding of p__memb_has, retaining its existential integer index.

(defun-sk mf15-p-memb-has-p (m pointer)
  (exists (index)
    (and
     (integerp index)
     (equal (mf15-memb-ptr m index) pointer)
     (<= 0 index)
     (< index (mf15-t2 (mf15-shift m 1))))))

;; Exact unfoldings of p__memb_allocated for the pre-update memory t_4 and
;; post-update memory t_3.

(defun mf15-p-memb-allocated-t4-p (m pointer)
  (and
   (not
    (equal
     (mf15-t4
      (mf15-shift
       (mf15-t5 (mf15-shift m 2))
       (mf15-memb-index m pointer)))
     0))
   (mf15-p-memb-has-p m pointer)))

(defun mf15-p-memb-allocated-t3-p (m pointer)
  (and
   (not
    (equal
     (mf15-t3
      (mf15-shift
       (mf15-t5 (mf15-shift m 2))
       (mf15-memb-index m pointer)))
     0))
   (mf15-p-memb-has-p m pointer)))

;; Source function equalities and Function.update are represented
;; extensionally over their complete typed domains.

(defun-sk mf15-t1-equals-t-p ()
  (forall (index)
    (implies
     (integerp index)
     (equal (mf15-t1 index) (mf15-t index)))))

(defun-sk mf15-t4-equals-t3-p ()
  (forall (address)
    (implies
     (mf15-address-p address)
     (equal (mf15-t4 address) (mf15-t3 address)))))

(defun-sk mf15-updated-t4-equals-t3-p (updated-address)
  (forall (address)
    (implies
     (mf15-address-p address)
     (equal
      (mf15-t3 address)
      (if (equal address updated-address)
          0
        (mf15-t4 address))))))

;; The source prior-payload-alias hypothesis remains universally quantified
;; over every mathematical integer below i.

(defun-sk
    mf15-no-earlier-payload-match-p
    (m payload-array bound pointer)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index bound))
     (not
      (equal
       (mf15-shift
        payload-array
        (* index (mf15-t2 (mf15-shift m 0))))
       pointer)))))

(defun-sk ntp4vc-memb-free-alloc-found-post-goal15-statement ()
  (forall
   (a1 i1 i a)
   (implies
    (and
     (mf15-function-types-p)
     (mf15-address-p a1)
     (integerp i1)
     (integerp i)
     (mf15-address-p a))
    (let*
        ((a2 (mf15-shift a1 1))
         (x (mf15-t2 a2))
         (a3 (mf15-shift a1 3))
         (a4 (mf15-shift a1 2))
         (a5 (mf15-shift (mf15-t5 a4) i1)))
      (implies
       (and
        (equal
         (mf15-memb-index a1 (mf15-memb-ptr a1 i))
         i)
        (<= 0 i)
        (<= i x)
        (<= (mf15-region (mf15-address-base a)) 0)
        (<= (mf15-region (mf15-address-base a1)) 0)
        (mf15-framed-p)
        (mf15-linked-p)
        (mf15-sconst-p)
        (mf15-is-sint32-p i)
        (mf15-is-sint32-p i1)
        (mf15-is-uint16-p x)
        (mf15-p-valid-memb-p a1)
        (mf15-p-memb-has-p a1 a)
        (mf15-valid-rd-t-p a3 1)
        (mf15-valid-rd-t-p a2 1)
        (mf15-p-memb-allocated-t4-p a1 a)
        (if (< i x)
            (and
             (equal i1 i)
             (mf15-t1-equals-t-p)
             (equal (mf15-memb-ptr a1 i1) a)
             (mf15-updated-t4-equals-t3-p a5)
             (mf15-valid-rd-t1-p a4 1)
             (mf15-valid-rd-t1-p a5 1)
             (mf15-valid-rw-t1-p a5 1))
          (mf15-t4-equals-t3-p))
        (mf15-no-earlier-payload-match-p
         a1 (mf15-t5 a3) i a))
       (not (mf15-p-memb-allocated-t3-p a1 a)))))))

(value-triple :itpeval-statement-checked)

:q
