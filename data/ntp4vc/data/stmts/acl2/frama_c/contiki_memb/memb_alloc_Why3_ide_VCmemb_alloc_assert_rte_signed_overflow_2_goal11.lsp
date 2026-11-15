;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_assert_rte_signed_overflow_2_goal11:
;; the signed 32-bit lower-bound safety obligation for the product of a memb
;; allocation index and element size under the allocation, framing, memory
;; validity, integer-range, and free-slot scan hypotheses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sov11-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sov11-address-base (address)
  (car address))

(defun sov11-address-offset (address)
  (cdr address))

(defun sov11-shift (address amount)
  (cons
   (sov11-address-base address)
   (+ (sov11-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_3, integer memories t_1 and t_2, allocation map t, and
;; the fixed region, linked, and sconst operations at those functions.

(defstub sov11-t3 (address) t)
(defstub sov11-t1 (address) t)
(defstub sov11-t2 (address) t)
(defstub sov11-malloc (index) t)
(defstub sov11-region (base) t)
(defstub sov11-linked-op () t)
(defstub sov11-sconst-op () t)

(defun-sk sov11-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (sov11-address-p address)
      (integerp index)
      (integerp base))
     (and
      (sov11-address-p (sov11-t3 address))
      (integerp (sov11-t1 address))
      (integerp (sov11-t2 address))
      (integerp (sov11-malloc index))
      (integerp (sov11-region base))))))

(defun sov11-linked-p ()
  (if (sov11-linked-op) t nil))

(defun sov11-sconst-p ()
  (if (sov11-sconst-op) t nil))

(defun sov11-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sov11-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun sov11-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (sov11-address-base address))
    (<= 0 (sov11-address-offset address))
    (<=
     (+ (sov11-address-offset address) length)
     (sov11-malloc (sov11-address-base address))))))

(defun sov11-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (sov11-address-base address)))
    (<= 0 (sov11-address-offset address))
    (<=
     (+ (sov11-address-offset address) length)
     (sov11-malloc (sov11-address-base address))))))

(defun sov11-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (sov11-address-base left)
     (sov11-address-base right)))
   (<=
    (+ (sov11-address-offset right) right-length)
    (sov11-address-offset left))
   (<=
    (+ (sov11-address-offset left) left-length)
    (sov11-address-offset right))))

(defun-sk sov11-framed-p ()
  (forall (address)
    (implies
     (sov11-address-p address)
     (<=
      (sov11-region
       (sov11-address-base (sov11-t3 address)))
      0))))

;; This is the exact unfolding of Axiomatic13.p_valid_memb.

(defun sov11-p-valid-memb-p (m)
  (let*
      ((element-size
        (sov11-t1 (sov11-shift m 0)))
       (element-count
        (sov11-t1 (sov11-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (sov11-t3 (sov11-shift m 2)))
       (payload-array
        (sov11-t3 (sov11-shift m 3)))
       (count-start (sov11-shift count-array 0))
       (payload-start (sov11-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (sov11-valid-rw-p m 4)
     (sov11-valid-rw-p count-array 1)
     (sov11-valid-rw-p payload-array 1)
     (sov11-valid-rw-p count-start element-count)
     (sov11-valid-rw-p payload-start payload-size)
     (sov11-separated-p
      count-start element-count payload-start payload-size))))

;; This preserves the source universal scan invariant over every integer i_1
;; below i.

(defun-sk sov11-earlier-slots-nonzero-p (array i)
  (forall (i1)
    (implies
     (and
      (integerp i1)
      (<= 0 i1)
      (< i1 i))
     (not
      (equal
       (sov11-t2 (sov11-shift array i1))
       0)))))

(defun-sk
    ntp4vc-memb-alloc-assert-rte-signed-overflow-2-goal11-statement ()
  (forall
   (a i)
   (implies
    (and
     (sov11-function-types-p)
     (sov11-address-p a)
     (integerp i))
    (let*
        ((a1 (sov11-shift a 2))
         (a2 (sov11-t3 a1))
         (a3 (sov11-shift a2 i))
         (a4 (sov11-shift a 1))
         (x (sov11-t1 a4))
         (x1 (sov11-t1 (sov11-shift a 0))))
      (implies
       (and
        (equal (sov11-t2 a3) 0)
        (<= 0 i)
        (< i x)
        (<= i x)
        (<= (sov11-region (sov11-address-base a)) 0)
        (sov11-framed-p)
        (sov11-linked-p)
        (sov11-sconst-p)
        (sov11-is-sint32-p i)
        (sov11-is-uint16-p x)
        (sov11-is-uint16-p x1)
        (sov11-p-valid-memb-p a)
        (sov11-valid-rd-p a1 1)
        (sov11-valid-rd-p a4 1)
        (sov11-valid-rd-p a3 1)
        (sov11-valid-rw-p a3 1)
        (sov11-earlier-slots-nonzero-p a2 i))
       (<= -2147483648 (* i x1)))))))

(value-triple :itpeval-statement-checked)

:q
