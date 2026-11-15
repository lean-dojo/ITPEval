;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/x509_parser/check_utf8_string_Why3_ide_VCcheck_utf8_string_assert_rte_mem_access_9_part03_goal29:
;; one-byte readability at the fourth UTF-8 parser address under the stated
;; byte-prefix, integer-range, allocation-validity, linking, and region
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun cus29-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun cus29-address-base (address)
  (car address))

(defun cus29-address-offset (address)
  (cdr address))

(defun cus29-shift (address amount)
  (cons
   (cus29-address-base address)
   (+ (cus29-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; allocation map t and byte memory t_1, together with the source region
;; function and the linked predicate specialized to t.

(defstub cus29-allocation (index) t)
(defstub cus29-byte-memory (address) t)
(defstub cus29-region (base) t)
(defstub cus29-linked-op () t)

(defun-sk cus29-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (cus29-address-p address)
      (integerp (cus29-byte-memory address)))
     (implies
      (integerp index)
      (integerp (cus29-allocation index)))
     (implies
      (integerp base)
      (integerp (cus29-region base))))))

(defun cus29-linked-p ()
  (if (cus29-linked-op) t nil))

;; Cbits.land is mathematical bitwise conjunction on unbounded integers.

(defun cus29-land (left right)
  (logand left right))

(defun cus29-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun cus29-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Exact unfolding of Memory.valid_rd for the allocation map t.

(defun cus29-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (cus29-address-base address)))
    (<= 0 (cus29-address-offset address))
    (<=
     (+ (cus29-address-offset address) length)
     (cus29-allocation (cus29-address-base address))))))

(defun-sk
    ntp4vc-check-utf8-string-assert-rte-mem-access-9-part03-goal29-statement
    ()
  (forall
   (a1 i i1 a)
   (implies
    (and
     (cus29-function-types-p)
     (cus29-address-p a1)
     (integerp i)
     (integerp i1)
     (cus29-address-p a))
    (let*
        ((a2 (cus29-shift a1 0))
         (a3 (cus29-shift a1 1))
         (x (cus29-byte-memory a3))
         (a4 (cus29-shift a1 2))
         (x1 (cus29-byte-memory a4))
         (a5 (cus29-shift a1 3)))
      (implies
       (and
        (not (equal i 0))
        (not (equal i1 0))
        (not (equal (cons 0 0) a))
        (equal (cus29-byte-memory a2) 244)
        (equal (cus29-land 192 x) 128)
        (equal (cus29-land 192 x1) 128)
        (<= 0 i1)
        (<= (cus29-region (cus29-address-base a)) 0)
        (<= 4 i)
        (<= 128 x)
        (<= x 143)
        (cus29-linked-p)
        (cus29-is-uint16-p i)
        (cus29-is-uint16-p i1)
        (cus29-is-uint8-p x)
        (cus29-is-uint8-p x1)
        (cus29-is-uint8-p (cus29-byte-memory a5))
        (cus29-valid-rd-p a2 1)
        (cus29-valid-rd-p a2 i)
        (cus29-valid-rd-p a3 1)
        (cus29-valid-rd-p a4 1)
        (implies
         (< 0 i1)
         (cus29-valid-rd-p (cus29-shift a 0) i1)))
       (cus29-valid-rd-p a5 1))))))

(value-triple :itpeval-statement-checked)

:q
