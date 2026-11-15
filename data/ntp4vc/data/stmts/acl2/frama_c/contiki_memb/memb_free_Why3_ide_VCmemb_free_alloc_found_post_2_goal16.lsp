;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_free_Why3_ide_VCmemb_free_alloc_found_post_2_goal16:
;; freeing an allocated memb slot increases the number of zero-valued slots
;; by exactly one under the stated memory, framing, range, validity, update,
;; and prior-slot hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun g16-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun g16-address-base (address)
  (car address))

(defun g16-address-offset (address)
  (cdr address))

(defun g16-shift (address amount)
  (cons
   (g16-address-base address)
   (+ (g16-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_2, pointer memory t_5, allocation maps t and t_1, and
;; integer memories t_4 and t_3. Region, linked, and sconst are the fixed
;; source operations applied to those arbitrary functions.

(defstub g16-t2 (address) t)
(defstub g16-t5 (address) t)
(defstub g16-t (index) t)
(defstub g16-t4 (address) t)
(defstub g16-t1 (index) t)
(defstub g16-t3 (address) t)
(defstub g16-region (base) t)
(defstub g16-linked-op () t)
(defstub g16-sconst-op () t)

(defun-sk g16-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (g16-address-p address)
      (and
       (integerp (g16-t2 address))
       (g16-address-p (g16-t5 address))
       (integerp (g16-t4 address))
       (integerp (g16-t3 address))))
     (implies
      (integerp index)
      (and
       (integerp (g16-t index))
       (integerp (g16-t1 index))))
     (implies
      (integerp base)
      (integerp (g16-region base))))))

(defun g16-linked-p ()
  (if (g16-linked-op) t nil))

(defun g16-sconst-p ()
  (if (g16-sconst-op) t nil))

(defun g16-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun g16-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Int.tdiv is truncating integer division. Its zero-divisor value is
;; irrelevant under p_valid_memb, which makes the divisor strictly positive.

(defun g16-tdiv (numerator denominator)
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

(defun g16-valid-rw-t-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (g16-address-base address))
    (<= 0 (g16-address-offset address))
    (<=
     (+ (g16-address-offset address) length)
     (g16-t (g16-address-base address))))))

(defun g16-valid-rd-t-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (g16-address-base address)))
    (<= 0 (g16-address-offset address))
    (<=
     (+ (g16-address-offset address) length)
     (g16-t (g16-address-base address))))))

(defun g16-valid-rw-t1-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (g16-address-base address))
    (<= 0 (g16-address-offset address))
    (<=
     (+ (g16-address-offset address) length)
     (g16-t1 (g16-address-base address))))))

(defun g16-valid-rd-t1-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (g16-address-base address)))
    (<= 0 (g16-address-offset address))
    (<=
     (+ (g16-address-offset address) length)
     (g16-t1 (g16-address-base address))))))

(defun g16-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (g16-address-base left)
     (g16-address-base right)))
   (<=
    (+ (g16-address-offset right) right-length)
    (g16-address-offset left))
   (<=
    (+ (g16-address-offset left) left-length)
    (g16-address-offset right))))

(defun-sk g16-framed-p ()
  (forall (address)
    (implies
     (g16-address-p address)
     (<=
      (g16-region
       (g16-address-base (g16-t5 address)))
      0))))

;; Exact unfoldings of the memb pointer and index functions.

(defun g16-memb-ptr (m index)
  (g16-shift
   (g16-t5 (g16-shift m 3))
   (* index (g16-t2 (g16-shift m 0)))))

(defun g16-memb-index (m pointer)
  (g16-tdiv
   (-
    (g16-address-offset pointer)
    (g16-address-offset
     (g16-t5 (g16-shift m 3))))
   (g16-t2 (g16-shift m 0))))

;; This is the exact unfolding of Axiomatic13.p_valid_memb.

(defun g16-p-valid-memb-p (m)
  (let*
      ((element-size
        (g16-t2 (g16-shift m 0)))
       (element-count
        (g16-t2 (g16-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (g16-t5 (g16-shift m 2)))
       (payload-array
        (g16-t5 (g16-shift m 3)))
       (count-start (g16-shift count-array 0))
       (payload-start (g16-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (g16-valid-rw-t-p m 4)
     (g16-valid-rw-t-p count-array 1)
     (g16-valid-rw-t-p payload-array 1)
     (g16-valid-rw-t-p count-start element-count)
     (g16-valid-rw-t-p payload-start payload-size)
     (g16-separated-p
      count-start element-count payload-start payload-size))))

;; Exact unfolding of p__memb_has, retaining its existential integer index.

(defun-sk g16-p-memb-has-p (m pointer)
  (exists (index)
    (and
     (integerp index)
     (equal (g16-memb-ptr m index) pointer)
     (<= 0 index)
     (< index (g16-t2 (g16-shift m 1))))))

(defun g16-p-memb-allocated-p (m pointer)
  (and
   (not
    (equal
     (g16-t4
      (g16-shift
       (g16-t5 (g16-shift m 2))
       (g16-memb-index m pointer)))
     0))
   (g16-p-memb-has-p m pointer)))

;; Source function equalities and Function.update are represented
;; extensionally over their complete typed domains.

(defun-sk g16-t1-equals-t-p ()
  (forall (index)
    (implies
     (integerp index)
     (equal (g16-t1 index) (g16-t index)))))

(defun-sk g16-t4-equals-t3-p ()
  (forall (address)
    (implies
     (g16-address-p address)
     (equal (g16-t4 address) (g16-t3 address)))))

(defun-sk g16-updated-t4-equals-t3-p (updated-address)
  (forall (address)
    (implies
     (g16-address-p address)
     (equal
      (g16-t3 address)
      (if (equal address updated-address)
          0
        (g16-t4 address))))))

;; The source prior-slot hypothesis remains universally quantified over every
;; mathematical integer below i.

(defun-sk g16-no-earlier-payload-match-p (m payload-array bound pointer)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index bound))
     (not
      (equal
       (g16-shift
        payload-array
        (* index (g16-t2 (g16-shift m 0))))
       pointer)))))

;; The source occurrence function is characterized by zero on empty intervals
;; and a one-step recurrence at the right endpoint. These terminating
;; recursions are that unique count for t_4 and t_3 respectively.

(defun g16-occ-t4-aux (array from remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if
         (equal
          (g16-t4
           (g16-shift array (+ from (1- remaining))))
          0)
         1
       0)
     (g16-occ-t4-aux array from (1- remaining)))))

(defun g16-occ-t3-aux (array from remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if
         (equal
          (g16-t3
           (g16-shift array (+ from (1- remaining))))
          0)
         1
       0)
     (g16-occ-t3-aux array from (1- remaining)))))

(defun g16-occ-t4 (array from to)
  (if
      (and
       (integerp from)
       (integerp to)
       (< from to))
      (g16-occ-t4-aux array from (- to from))
    0))

(defun g16-occ-t3 (array from to)
  (if
      (and
       (integerp from)
       (integerp to)
       (< from to))
      (g16-occ-t3-aux array from (- to from))
    0))

(defun g16-numfree-t4 (m)
  (g16-occ-t4
   (g16-t5 (g16-shift m 2))
   0
   (g16-t2 (g16-shift m 1))))

(defun g16-numfree-t3 (m)
  (g16-occ-t3
   (g16-t5 (g16-shift m 2))
   0
   (g16-t2 (g16-shift m 1))))

(defun-sk
    ntp4vc-memb-free-alloc-found-post-2-goal16-statement ()
  (forall
   (a1 i1 i a)
   (implies
    (and
     (g16-function-types-p)
     (g16-address-p a1)
     (integerp i1)
     (integerp i)
     (g16-address-p a))
    (let*
        ((a2 (g16-shift a1 1))
         (x (g16-t2 a2))
         (a3 (g16-shift a1 3))
         (a4 (g16-shift a1 2))
         (a5 (g16-shift (g16-t5 a4) i1)))
      (implies
       (and
        (equal
         (g16-memb-index a1 (g16-memb-ptr a1 i))
         i)
        (<= 0 i)
        (<= i x)
        (<= (g16-region (g16-address-base a)) 0)
        (<= (g16-region (g16-address-base a1)) 0)
        (g16-framed-p)
        (g16-linked-p)
        (g16-sconst-p)
        (g16-is-sint32-p i)
        (g16-is-sint32-p i1)
        (g16-is-uint16-p x)
        (g16-p-valid-memb-p a1)
        (g16-p-memb-has-p a1 a)
        (g16-valid-rd-t-p a3 1)
        (g16-valid-rd-t-p a2 1)
        (g16-p-memb-allocated-p a1 a)
        (if (< i x)
            (and
             (equal i1 i)
             (g16-t1-equals-t-p)
             (equal (g16-memb-ptr a1 i1) a)
             (g16-updated-t4-equals-t3-p a5)
             (g16-valid-rd-t1-p a4 1)
             (g16-valid-rd-t1-p a5 1)
             (g16-valid-rw-t1-p a5 1))
          (g16-t4-equals-t3-p))
        (g16-no-earlier-payload-match-p
         a1 (g16-t5 a3) i a))
       (equal
        (+ 1 (g16-numfree-t4 a1))
        (g16-numfree-t3 a1)))))))

(value-triple :itpeval-statement-checked)

:q
