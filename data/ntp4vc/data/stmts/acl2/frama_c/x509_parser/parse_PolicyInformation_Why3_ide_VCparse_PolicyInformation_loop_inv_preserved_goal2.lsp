;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/x509_parser/parse_PolicyInformation_Why3_ide_VCparse_PolicyInformation_loop_inv_preserved_goal2:
;; preservation of readable memory for the remaining PolicyInformation segment
;; under the stated integer bounds, linking, region, and validity hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ppi2-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ppi2-address-base (address)
  (car address))

(defun ppi2-address-offset (address)
  (cdr address))

(defun ppi2-shift (address amount)
  (cons
   (ppi2-address-base address)
   (+ (ppi2-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; allocation map t, the fixed source region function, and the linked
;; proposition specialized to t.

(defstub ppi2-allocation (index) t)
(defstub ppi2-region (base) t)
(defstub ppi2-linked-op () t)

(defun-sk ppi2-function-types-p ()
  (forall (index base)
    (and
     (implies
      (integerp index)
      (integerp (ppi2-allocation index)))
     (implies
      (integerp base)
      (integerp (ppi2-region base))))))

(defun ppi2-linked-p ()
  (if (ppi2-linked-op) t nil))

(defun ppi2-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Exact unfoldings of Memory.valid_rw and Memory.valid_rd for t.

(defun ppi2-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (ppi2-address-base address))
    (<= 0 (ppi2-address-offset address))
    (<=
     (+ (ppi2-address-offset address) length)
     (ppi2-allocation (ppi2-address-base address))))))

(defun ppi2-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (ppi2-address-base address)))
    (<= 0 (ppi2-address-offset address))
    (<=
     (+ (ppi2-address-offset address) length)
     (ppi2-allocation (ppi2-address-base address))))))

(defun-sk
    ntp4vc-parse-policyinformation-loop-inv-preserved-goal2-statement ()
  (forall
   (a1 a i4 i5 i i1 i2 i3 a2 i6)
   (implies
    (and
     (ppi2-function-types-p)
     (ppi2-address-p a1)
     (ppi2-address-p a)
     (integerp i4)
     (integerp i5)
     (integerp i)
     (integerp i1)
     (integerp i2)
     (integerp i3)
     (ppi2-address-p a2)
     (integerp i6))
    (let
        ((x (ppi2-address-base a1))
         (x1 (ppi2-address-base a))
         (a3 (ppi2-shift a1 i4))
         (a4 (ppi2-shift a1 (+ i4 i5 (- i))))
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
        (<= (ppi2-region x1) 0)
        (<= (ppi2-region x) 0)
        (<= -2147483648 i)
        (<= -2147483648 i6)
        (<= 2 i2)
        (<= 2 i4)
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
        (<= (+ 3 i) i5)
        (ppi2-linked-p)
        (ppi2-is-uint16-p i)
        (ppi2-is-uint16-p i1)
        (ppi2-is-uint16-p i2)
        (ppi2-is-uint16-p i3)
        (ppi2-is-uint16-p i4)
        (ppi2-is-uint16-p i5)
        (ppi2-is-uint16-p i6)
        (ppi2-valid-rw-p a 1)
        (ppi2-is-uint16-p (- i i6))
        (ppi2-is-uint16-p x4)
        (ppi2-is-uint16-p (- i5 i))
        (ppi2-valid-rd-p (ppi2-shift a2 0) i1)
        (implies
         (< 0 i3)
         (ppi2-valid-rd-p (ppi2-shift a1 0) i3))
        (implies
         (< 0 i5)
         (ppi2-valid-rd-p a3 i5))
        (implies
         (< 0 i)
         (ppi2-valid-rd-p a4 i)))
       (ppi2-valid-rd-p (ppi2-shift a2 i2) x4))))))

(value-triple :itpeval-statement-checked)

:q
