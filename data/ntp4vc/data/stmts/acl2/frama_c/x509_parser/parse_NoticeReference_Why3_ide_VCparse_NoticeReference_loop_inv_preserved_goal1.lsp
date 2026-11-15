;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/x509_parser/parse_NoticeReference_Why3_ide_VCparse_NoticeReference_loop_inv_preserved_goal1:
;; preservation of readable memory for the remaining NoticeReference segment
;; under the stated integer bounds, linking, region, and validity hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun pnr1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun pnr1-address-base (address)
  (car address))

(defun pnr1-address-offset (address)
  (cdr address))

(defun pnr1-shift (address amount)
  (cons
   (pnr1-address-base address)
   (+ (pnr1-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; allocation map t, the fixed source region function, and the linked
;; proposition specialized to t.

(defstub pnr1-allocation (index) t)
(defstub pnr1-region (base) t)
(defstub pnr1-linked-op () t)

(defun-sk pnr1-function-types-p ()
  (forall (index base)
    (and
     (implies
      (integerp index)
      (integerp (pnr1-allocation index)))
     (implies
      (integerp base)
      (integerp (pnr1-region base))))))

(defun pnr1-linked-p ()
  (if (pnr1-linked-op) t nil))

(defun pnr1-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Exact unfoldings of Memory.valid_rw and Memory.valid_rd for t.

(defun pnr1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (pnr1-address-base address))
    (<= 0 (pnr1-address-offset address))
    (<=
     (+ (pnr1-address-offset address) length)
     (pnr1-allocation (pnr1-address-base address))))))

(defun pnr1-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (pnr1-address-base address)))
    (<= 0 (pnr1-address-offset address))
    (<=
     (+ (pnr1-address-offset address) length)
     (pnr1-allocation (pnr1-address-base address))))))

(defun-sk
    ntp4vc-parse-noticereference-loop-inv-preserved-goal1-statement ()
  (forall
   (a1 a i4 i5 i i1 i2 i3 a2 i6)
   (implies
    (and
     (pnr1-function-types-p)
     (pnr1-address-p a1)
     (pnr1-address-p a)
     (integerp i4)
     (integerp i5)
     (integerp i)
     (integerp i1)
     (integerp i2)
     (integerp i3)
     (pnr1-address-p a2)
     (integerp i6))
    (let
        ((x (pnr1-address-base a1))
         (x1 (pnr1-address-base a))
         (a3 (pnr1-shift a1 i4))
         (a4 (pnr1-shift a1 (+ i4 i5 (- i))))
         (x3 (+ i4 i5))
         (x4 (- i1 i2)))
      (implies
       (and
        (not (equal i 0))
        (not (equal i1 0))
        (not (equal i3 0))
        (not (equal i5 0))
        (not (equal (cons 0 0) a1))
        (not (equal (cons 0 0) a2))
        (not (equal x x1))
        (not (equal a3 (cons 0 0)))
        (not (equal a4 (cons 0 0)))
        (<= 0 i)
        (<= i6 i)
        (<= 0 i1)
        (<= i2 i1)
        (<= 0 i3)
        (<= i4 i3)
        (<= i5 i3)
        (<= 0 i5)
        (<= 0 i6)
        (<= x3 i3)
        (<= 0 x3)
        (<= (pnr1-region x1) 0)
        (<= (pnr1-region x) 0)
        (<= -2147483648 i)
        (<= -2147483648 i6)
        (<= 2 i4)
        (<= 3 i2)
        (<= i 65535)
        (<= i6 65535)
        (<= i 2147483647)
        (<= i6 2147483647)
        (<= -2147483648 x3)
        (<= x3 65535)
        (<= x3 2147483647)
        (<= (+ 2 i6) i)
        (<= i1 (+ 65535 i2))
        (<= i1 (+ 2147483647 i2))
        (<= i2 (+ 2147483648 i1))
        (pnr1-linked-p)
        (pnr1-is-uint16-p i)
        (pnr1-is-uint16-p i1)
        (pnr1-is-uint16-p i2)
        (pnr1-is-uint16-p i3)
        (pnr1-is-uint16-p i4)
        (pnr1-is-uint16-p i5)
        (pnr1-is-uint16-p i6)
        (pnr1-valid-rw-p a 1)
        (pnr1-is-uint16-p (- i i6))
        (pnr1-is-uint16-p x4)
        (pnr1-is-uint16-p (- i5 i))
        (pnr1-valid-rd-p (pnr1-shift a2 0) i1)
        (implies
         (< 0 i3)
         (pnr1-valid-rd-p (pnr1-shift a1 0) i3))
        (implies
         (< 0 i5)
         (pnr1-valid-rd-p a3 i5))
        (implies
         (< 0 i)
         (pnr1-valid-rd-p a4 i)))
       (pnr1-valid-rd-p (pnr1-shift a2 i2) x4))))))

(value-triple :itpeval-statement-checked)

:q
