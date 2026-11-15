;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_loop_inv_2_preserved_goal4:
;; preservation of the nonzero memb allocation-scan invariant at an index no
;; greater than the current scan position, under the stated memory, framing,
;; integer-range, and validity hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun g4-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun g4-address-base (address)
  (car address))

(defun g4-address-offset (address)
  (cdr address))

(defun g4-shift (address amount)
  (cons
   (g4-address-base address)
   (+ (g4-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer function t_3, integer memories t_1 and t_2, allocation map t,
;; region function, and the linked and sconst predicates at those functions.

(defstub g4-t3 (address) t)
(defstub g4-t1 (address) t)
(defstub g4-t2 (address) t)
(defstub g4-allocation (index) t)
(defstub g4-region (base) t)
(defstub g4-linked-op () t)
(defstub g4-sconst-op () t)

(defun-sk g4-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (g4-address-p address)
      (and
       (g4-address-p (g4-t3 address))
       (integerp (g4-t1 address))
       (integerp (g4-t2 address))))
     (implies
      (integerp index)
      (integerp (g4-allocation index)))
     (implies
      (integerp base)
      (integerp (g4-region base))))))

(defun g4-linked-p ()
  (if (g4-linked-op) t nil))

(defun g4-sconst-p ()
  (if (g4-sconst-op) t nil))

(defun g4-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun g4-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun g4-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun g4-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (g4-address-base address))
    (<= 0 (g4-address-offset address))
    (<=
     (+ (g4-address-offset address) length)
     (g4-allocation (g4-address-base address))))))

(defun g4-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (g4-address-base address)))
    (<= 0 (g4-address-offset address))
    (<=
     (+ (g4-address-offset address) length)
     (g4-allocation (g4-address-base address))))))

(defun g4-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (g4-address-base left)
     (g4-address-base right)))
   (<=
    (+ (g4-address-offset right) right-length)
    (g4-address-offset left))
   (<=
    (+ (g4-address-offset left) left-length)
    (g4-address-offset right))))

(defun-sk g4-framed-p ()
  (forall (address)
    (implies
     (g4-address-p address)
     (<=
      (g4-region
       (g4-address-base (g4-t3 address)))
      0))))

;; Exact unfolding of Axiomatic13.p_valid_memb.

(defun g4-p-valid-memb-p (m)
  (let*
      ((element-size
        (g4-t1 (g4-shift m 0)))
       (element-count
        (g4-t1 (g4-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (g4-t3 (g4-shift m 2)))
       (payload-array
        (g4-t3 (g4-shift m 3)))
       (count-start (g4-shift count-array 0))
       (payload-start (g4-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (g4-valid-rw-p m 4)
     (g4-valid-rw-p count-array 1)
     (g4-valid-rw-p payload-array 1)
     (g4-valid-rw-p count-start element-count)
     (g4-valid-rw-p payload-start payload-size)
     (g4-separated-p
      count-start element-count payload-start payload-size))))

;; The source loop invariant remains universally quantified over every
;; mathematical integer index strictly before the current scan position.

(defun-sk g4-earlier-slots-nonzero-p (array bound)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index bound))
     (not
      (equal
       (g4-t2 (g4-shift array index))
       0)))))

(defun-sk
    ntp4vc-memb-alloc-loop-inv-2-preserved-goal4-statement ()
  (forall
   (a i i1)
   (implies
    (and
     (g4-function-types-p)
     (g4-address-p a)
     (integerp i)
     (integerp i1))
    (let*
        ((a1 (g4-shift a 2))
         (a2 (g4-t3 a1))
         (a3 (g4-shift a2 i))
         (x (g4-t2 a3))
         (a4 (g4-shift a 1))
         (x1 (g4-t1 a4)))
      (implies
       (and
        (not (equal x 0))
        (<= 0 i)
        (<= i1 i)
        (<= 0 i1)
        (< i x1)
        (<= i x1)
        (<= (g4-region (g4-address-base a)) 0)
        (<= i 2147483646)
        (g4-framed-p)
        (g4-linked-p)
        (g4-sconst-p)
        (g4-is-sint32-p i)
        (g4-is-sint32-p i1)
        (g4-is-uint16-p x1)
        (g4-is-sint32-p (+ 1 i))
        (g4-p-valid-memb-p a)
        (g4-valid-rd-p a1 1)
        (g4-valid-rd-p a4 1)
        (g4-is-sint8-p x)
        (g4-valid-rd-p a3 1)
        (g4-earlier-slots-nonzero-p a2 i))
       (not
        (equal
         (g4-t2 (g4-shift a2 i1))
         0)))))))

(value-triple :itpeval-statement-checked)

:q
