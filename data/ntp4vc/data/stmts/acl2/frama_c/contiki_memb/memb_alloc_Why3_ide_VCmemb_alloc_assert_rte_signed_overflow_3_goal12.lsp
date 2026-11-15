;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_assert_rte_signed_overflow_3_goal12:
;; the signed 32-bit upper-bound safety obligation for the product of a memb
;; allocation index and element size under the allocation, framing, memory
;; validity, integer-range, and free-slot scan hypotheses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sov12-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sov12-address-base (address)
  (car address))

(defun sov12-address-offset (address)
  (cdr address))

(defun sov12-shift (address amount)
  (cons
   (sov12-address-base address)
   (+ (sov12-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_3, integer memories t_1 and t_2, allocation map t, and
;; the fixed region, linked, and sconst operations at those functions.

(defstub sov12-t3 (address) t)
(defstub sov12-t1 (address) t)
(defstub sov12-t2 (address) t)
(defstub sov12-malloc (index) t)
(defstub sov12-region (base) t)
(defstub sov12-linked-op () t)
(defstub sov12-sconst-op () t)

(defun-sk sov12-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (sov12-address-p address)
      (integerp index)
      (integerp base))
     (and
      (sov12-address-p (sov12-t3 address))
      (integerp (sov12-t1 address))
      (integerp (sov12-t2 address))
      (integerp (sov12-malloc index))
      (integerp (sov12-region base))))))

(defun sov12-linked-p ()
  (if (sov12-linked-op) t nil))

(defun sov12-sconst-p ()
  (if (sov12-sconst-op) t nil))

(defun sov12-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sov12-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun sov12-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (sov12-address-base address))
    (<= 0 (sov12-address-offset address))
    (<=
     (+ (sov12-address-offset address) length)
     (sov12-malloc (sov12-address-base address))))))

(defun sov12-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (sov12-address-base address)))
    (<= 0 (sov12-address-offset address))
    (<=
     (+ (sov12-address-offset address) length)
     (sov12-malloc (sov12-address-base address))))))

(defun sov12-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (sov12-address-base left)
     (sov12-address-base right)))
   (<=
    (+ (sov12-address-offset right) right-length)
    (sov12-address-offset left))
   (<=
    (+ (sov12-address-offset left) left-length)
    (sov12-address-offset right))))

(defun-sk sov12-framed-p ()
  (forall (address)
    (implies
     (sov12-address-p address)
     (<=
      (sov12-region
       (sov12-address-base (sov12-t3 address)))
      0))))

;; This is the exact unfolding of Axiomatic13.p_valid_memb.

(defun sov12-p-valid-memb-p (m)
  (let*
      ((element-size
        (sov12-t1 (sov12-shift m 0)))
       (element-count
        (sov12-t1 (sov12-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (sov12-t3 (sov12-shift m 2)))
       (payload-array
        (sov12-t3 (sov12-shift m 3)))
       (count-start (sov12-shift count-array 0))
       (payload-start (sov12-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (sov12-valid-rw-p m 4)
     (sov12-valid-rw-p count-array 1)
     (sov12-valid-rw-p payload-array 1)
     (sov12-valid-rw-p count-start element-count)
     (sov12-valid-rw-p payload-start payload-size)
     (sov12-separated-p
      count-start element-count payload-start payload-size))))

;; This preserves the source universal scan invariant over every integer i_1
;; below i.

(defun-sk sov12-earlier-slots-nonzero-p (array i)
  (forall (i1)
    (implies
     (and
      (integerp i1)
      (<= 0 i1)
      (< i1 i))
     (not
      (equal
       (sov12-t2 (sov12-shift array i1))
       0)))))

(defun-sk
    ntp4vc-memb-alloc-assert-rte-signed-overflow-3-goal12-statement ()
  (forall
   (a i)
   (implies
    (and
     (sov12-function-types-p)
     (sov12-address-p a)
     (integerp i))
    (let*
        ((a1 (sov12-shift a 2))
         (a2 (sov12-t3 a1))
         (a3 (sov12-shift a2 i))
         (a4 (sov12-shift a 1))
         (x (sov12-t1 a4))
         (x1 (sov12-t1 (sov12-shift a 0))))
      (implies
       (and
        (equal (sov12-t2 a3) 0)
        (<= 0 i)
        (< i x)
        (<= i x)
        (<= (sov12-region (sov12-address-base a)) 0)
        (sov12-framed-p)
        (sov12-linked-p)
        (sov12-sconst-p)
        (sov12-is-sint32-p i)
        (sov12-is-uint16-p x)
        (sov12-is-uint16-p x1)
        (sov12-p-valid-memb-p a)
        (sov12-valid-rd-p a1 1)
        (sov12-valid-rd-p a4 1)
        (sov12-valid-rd-p a3 1)
        (sov12-valid-rw-p a3 1)
        (sov12-earlier-slots-nonzero-p a2 i))
       (<= (* i x1) 2147483647))))))

(value-triple :itpeval-statement-checked)

:q
