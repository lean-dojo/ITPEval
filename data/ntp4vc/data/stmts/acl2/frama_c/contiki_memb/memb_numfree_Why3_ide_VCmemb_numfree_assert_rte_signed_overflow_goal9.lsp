;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_numfree_Why3_ide_VCmemb_numfree_assert_rte_signed_overflow_goal9:
;; the signed 32-bit upper-bound safety obligation for the number of
;; zero-valued memb slots preceding a selected free slot, under the stated
;; framing, memory-validity, and integer-range hypotheses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun nf9-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun nf9-address-base (address)
  (car address))

(defun nf9-address-offset (address)
  (cdr address))

(defun nf9-shift (address amount)
  (cons
   (nf9-address-base address)
   (+ (nf9-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_3, integer memories t_1 and t_2, allocation map t, region
;; function, and the linked and sconst predicates at the functions occurring
;; in this verification condition.

(defstub nf9-t3 (address) t)
(defstub nf9-t1 (address) t)
(defstub nf9-t2 (address) t)
(defstub nf9-allocation (index) t)
(defstub nf9-region (base) t)
(defstub nf9-linked-op () t)
(defstub nf9-sconst-op () t)

(defun-sk nf9-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (nf9-address-p address)
      (and
       (nf9-address-p (nf9-t3 address))
       (integerp (nf9-t1 address))
       (integerp (nf9-t2 address))))
     (implies
      (integerp index)
      (integerp (nf9-allocation index)))
     (implies
      (integerp base)
      (integerp (nf9-region base))))))

(defun nf9-linked-p ()
  (if (nf9-linked-op) t nil))

(defun nf9-sconst-p ()
  (if (nf9-sconst-op) t nil))

(defun nf9-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun nf9-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun nf9-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (nf9-address-base address))
    (<= 0 (nf9-address-offset address))
    (<=
     (+ (nf9-address-offset address) length)
     (nf9-allocation (nf9-address-base address))))))

(defun nf9-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (nf9-address-base address)))
    (<= 0 (nf9-address-offset address))
    (<=
     (+ (nf9-address-offset address) length)
     (nf9-allocation (nf9-address-base address))))))

(defun nf9-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (nf9-address-base left)
     (nf9-address-base right)))
   (<=
    (+ (nf9-address-offset right) right-length)
    (nf9-address-offset left))
   (<=
    (+ (nf9-address-offset left) left-length)
    (nf9-address-offset right))))

(defun-sk nf9-framed-p ()
  (forall (address)
    (implies
     (nf9-address-p address)
     (<=
      (nf9-region
       (nf9-address-base (nf9-t3 address)))
      0))))

;; Exact unfolding of Axiomatic13.p_valid_memb.

(defun nf9-p-valid-memb-p (m)
  (let*
      ((element-size
        (nf9-t1 (nf9-shift m 0)))
       (element-count
        (nf9-t1 (nf9-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (nf9-t3 (nf9-shift m 2)))
       (payload-array
        (nf9-t3 (nf9-shift m 3)))
       (count-start (nf9-shift count-array 0))
       (payload-start (nf9-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (nf9-valid-rw-p m 4)
     (nf9-valid-rw-p count-array 1)
     (nf9-valid-rw-p payload-array 1)
     (nf9-valid-rw-p count-start element-count)
     (nf9-valid-rw-p payload-start payload-size)
     (nf9-separated-p
      count-start element-count payload-start payload-size))))

;; The source occurrence function is characterized by zero on empty intervals
;; and a one-step recurrence at the right endpoint. This terminating recursion
;; is that unique zero count for t_2.

(defun nf9-occ-t2-aux (array from remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if
         (equal
          (nf9-t2
           (nf9-shift array (+ from (1- remaining))))
          0)
         1
       0)
     (nf9-occ-t2-aux array from (1- remaining)))))

(defun nf9-occ-t2 (array from to)
  (if
      (and
       (integerp from)
       (integerp to)
       (< from to))
      (nf9-occ-t2-aux array from (- to from))
    0))

(defun-sk
    ntp4vc-memb-numfree-assert-rte-signed-overflow-goal9-statement ()
  (forall
   (a i)
   (implies
    (and
     (nf9-function-types-p)
     (nf9-address-p a)
     (integerp i))
    (let*
        ((a1 (nf9-shift a 2))
         (a2 (nf9-t3 a1))
         (a3 (nf9-shift a2 i))
         (a4 (nf9-shift a 1))
         (x (nf9-t1 a4))
         (x1 (nf9-occ-t2 a2 0 i)))
      (implies
       (and
        (equal (nf9-t2 a3) 0)
        (<= 0 i)
        (< i x)
        (<= i x)
        (<= (nf9-region (nf9-address-base a)) 0)
        (<= x1 i)
        (nf9-framed-p)
        (nf9-linked-p)
        (nf9-sconst-p)
        (nf9-is-sint32-p i)
        (nf9-is-uint16-p x)
        (nf9-p-valid-memb-p a)
        (nf9-valid-rd-p a1 1)
        (nf9-valid-rd-p a4 1)
        (nf9-valid-rd-p a3 1)
        (nf9-is-sint32-p x1))
       (<= x1 2147483646))))))

(value-triple :itpeval-statement-checked)

:q
