;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_assert_rte_mem_access_8_goal10:
;; readability of a memb control field under the allocation, framing, memory
;; validity, integer-range, and free-slot scan hypotheses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun marg10-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun marg10-address-base (address)
  (car address))

(defun marg10-address-offset (address)
  (cdr address))

(defun marg10-shift (address amount)
  (cons
   (marg10-address-base address)
   (+ (marg10-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_3, integer memories t_1 and t_2, allocation map t, and
;; the fixed region, linked, and sconst operations at those functions.

(defstub marg10-t3 (address) t)
(defstub marg10-t1 (address) t)
(defstub marg10-t2 (address) t)
(defstub marg10-malloc (index) t)
(defstub marg10-region (base) t)
(defstub marg10-linked-op () t)
(defstub marg10-sconst-op () t)

(defun-sk marg10-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (marg10-address-p address)
      (integerp index)
      (integerp base))
     (and
      (marg10-address-p (marg10-t3 address))
      (integerp (marg10-t1 address))
      (integerp (marg10-t2 address))
      (integerp (marg10-malloc index))
      (integerp (marg10-region base))))))

(defun marg10-linked-p ()
  (if (marg10-linked-op) t nil))

(defun marg10-sconst-p ()
  (if (marg10-sconst-op) t nil))

(defun marg10-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun marg10-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun marg10-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (marg10-address-base address))
    (<= 0 (marg10-address-offset address))
    (<=
     (+ (marg10-address-offset address) length)
     (marg10-malloc (marg10-address-base address))))))

(defun marg10-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (marg10-address-base address)))
    (<= 0 (marg10-address-offset address))
    (<=
     (+ (marg10-address-offset address) length)
     (marg10-malloc (marg10-address-base address))))))

(defun marg10-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (marg10-address-base left)
     (marg10-address-base right)))
   (<=
    (+ (marg10-address-offset right) right-length)
    (marg10-address-offset left))
   (<=
    (+ (marg10-address-offset left) left-length)
    (marg10-address-offset right))))

(defun-sk marg10-framed-p ()
  (forall (address)
    (implies
     (marg10-address-p address)
     (<=
      (marg10-region
       (marg10-address-base (marg10-t3 address)))
      0))))

;; This is the exact unfolding of Axiomatic13.p_valid_memb.

(defun marg10-p-valid-memb-p (m)
  (let*
      ((element-size
        (marg10-t1 (marg10-shift m 0)))
       (element-count
        (marg10-t1 (marg10-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (marg10-t3 (marg10-shift m 2)))
       (payload-array
        (marg10-t3 (marg10-shift m 3)))
       (count-start (marg10-shift count-array 0))
       (payload-start (marg10-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (marg10-valid-rw-p m 4)
     (marg10-valid-rw-p count-array 1)
     (marg10-valid-rw-p payload-array 1)
     (marg10-valid-rw-p count-start element-count)
     (marg10-valid-rw-p payload-start payload-size)
     (marg10-separated-p
      count-start element-count payload-start payload-size))))

;; This preserves the source universal scan invariant over every integer i_1
;; below i.

(defun-sk marg10-earlier-slots-nonzero-p (array i)
  (forall (i1)
    (implies
     (and
      (integerp i1)
      (<= 0 i1)
      (< i1 i))
     (not
      (equal
       (marg10-t2 (marg10-shift array i1))
       0)))))

(defun-sk
    ntp4vc-memb-alloc-assert-rte-mem-access-8-goal10-statement ()
  (forall
   (a i)
   (implies
    (and
     (marg10-function-types-p)
     (marg10-address-p a)
     (integerp i))
    (let*
        ((a1 (marg10-shift a 2))
         (a2 (marg10-t3 a1))
         (a3 (marg10-shift a2 i))
         (a4 (marg10-shift a 1))
         (x (marg10-t1 a4)))
      (implies
       (and
        (equal (marg10-t2 a3) 0)
        (<= 0 i)
        (< i x)
        (<= i x)
        (<= (marg10-region (marg10-address-base a)) 0)
        (marg10-framed-p)
        (marg10-linked-p)
        (marg10-sconst-p)
        (marg10-is-sint32-p i)
        (marg10-is-uint16-p x)
        (marg10-p-valid-memb-p a)
        (marg10-valid-rd-p a1 1)
        (marg10-valid-rd-p a4 1)
        (marg10-valid-rd-p a3 1)
        (marg10-valid-rw-p a3 1)
        (marg10-earlier-slots-nonzero-p a2 i))
       (marg10-valid-rd-p (marg10-shift a 0) 1))))))

(value-triple :itpeval-statement-checked)

:q
