;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/x509_parser/check_utf8_string_Why3_ide_VCcheck_utf8_string_assert_rte_mem_access_7_part04_goal20:
;; one-byte readability at the next UTF-8 parser address under the stated
;; integer bounds, allocation validity, linking, and region hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun cus20-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun cus20-address-base (address)
  (car address))

(defun cus20-address-offset (address)
  (cdr address))

(defun cus20-shift (address amount)
  (cons
   (cus20-address-base address)
   (+ (cus20-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; allocation map t and byte memory t_1, together with the source region
;; function and the linked predicate specialized to t.

(defstub cus20-allocation (index) t)
(defstub cus20-byte-memory (address) t)
(defstub cus20-region (base) t)
(defstub cus20-linked-op () t)

(defun-sk cus20-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (cus20-address-p address)
      (integerp (cus20-byte-memory address)))
     (implies
      (integerp index)
      (integerp (cus20-allocation index)))
     (implies
      (integerp base)
      (integerp (cus20-region base))))))

(defun cus20-linked-p ()
  (if (cus20-linked-op) t nil))

(defun cus20-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun cus20-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Exact unfolding of Memory.valid_rd for the allocation map t.

(defun cus20-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (cus20-address-base address)))
    (<= 0 (cus20-address-offset address))
    (<=
     (+ (cus20-address-offset address) length)
     (cus20-allocation (cus20-address-base address))))))

(defun-sk
    ntp4vc-check-utf8-string-assert-rte-mem-access-7-part04-goal20-statement
    ()
  (forall
   (a1 i i1 a)
   (implies
    (and
     (cus20-function-types-p)
     (cus20-address-p a1)
     (integerp i)
     (integerp i1)
     (cus20-address-p a))
    (let*
        ((a2 (cus20-shift a1 0))
         (x (cus20-byte-memory a2)))
      (implies
       (and
        (not (equal i 0))
        (not (equal i1 0))
        (not (equal (cons 0 0) a))
        (not (equal x 240))
        (not (equal x 244))
        (<= 0 i1)
        (<= (cus20-region (cus20-address-base a)) 0)
        (<= 4 i)
        (<= 128 x)
        (<= 194 x)
        (<= 224 x)
        (<= 240 x)
        (<= x 244)
        (cus20-linked-p)
        (cus20-is-uint16-p i)
        (cus20-is-uint16-p i1)
        (cus20-is-uint8-p x)
        (cus20-valid-rd-p a2 1)
        (cus20-valid-rd-p a2 i)
        (implies
         (< 0 i1)
         (cus20-valid-rd-p (cus20-shift a 0) i1)))
       (cus20-valid-rd-p (cus20-shift a1 1) 1))))))

(value-triple :itpeval-statement-checked)

:q
