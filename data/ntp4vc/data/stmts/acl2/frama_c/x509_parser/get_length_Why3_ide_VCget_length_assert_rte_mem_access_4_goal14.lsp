;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/x509_parser/get_length_Why3_ide_VCget_length_assert_rte_mem_access_4_goal14:
;; one-byte readability two bytes past a parser address under the stated
;; integer-range, memory-validity, linking, region, and bit hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun gl14-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun gl14-address-base (address)
  (car address))

(defun gl14-address-offset (address)
  (cdr address))

(defun gl14-shift (address amount)
  (cons
   (gl14-address-base address)
   (+ (gl14-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; allocation map t and byte memory t_1, together with the source region
;; function and the linked predicate specialized to t.

(defstub gl14-allocation (index) t)
(defstub gl14-byte-memory (address) t)
(defstub gl14-region (base) t)
(defstub gl14-linked-op () t)

(defun-sk gl14-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (gl14-address-p address)
      (integerp (gl14-byte-memory address)))
     (implies
      (integerp index)
      (integerp (gl14-allocation index)))
     (implies
      (integerp base)
      (integerp (gl14-region base))))))

(defun gl14-linked-p ()
  (if (gl14-linked-op) t nil))

;; Cbits.land and Cbits.bit_test are mathematical bit operations on
;; unbounded integers.

(defun gl14-land (left right)
  (logand left right))

(defun gl14-bit-test-p (value position)
  (and
   (integerp value)
   (integerp position)
   (<= 0 position)
   (logbitp position value)))

(defun gl14-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun gl14-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Exact unfoldings of Memory.valid_rw and Memory.valid_rd for t.

(defun gl14-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (gl14-address-base address))
    (<= 0 (gl14-address-offset address))
    (<=
     (+ (gl14-address-offset address) length)
     (gl14-allocation (gl14-address-base address))))))

(defun gl14-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (gl14-address-base address)))
    (<= 0 (gl14-address-offset address))
    (<=
     (+ (gl14-address-offset address) length)
     (gl14-allocation (gl14-address-base address))))))

(defun-sk
    ntp4vc-get-length-assert-rte-mem-access-4-goal14-statement ()
  (forall
   (a1 a a2 i)
   (implies
    (and
     (gl14-function-types-p)
     (gl14-address-p a1)
     (gl14-address-p a)
     (gl14-address-p a2)
     (integerp i))
    (let*
        ((x (gl14-address-base a1))
         (x1 (gl14-address-base a))
         (x2 (gl14-address-base a2))
         (a3 (gl14-shift a1 0))
         (x3 (gl14-byte-memory a3)))
      (implies
       (and
        (not (equal i 0))
        (not (equal a2 a))
        (not (equal (cons 0 0) a1))
        (not (equal x x1))
        (not (equal x2 x))
        (not (equal x3 128))
        (equal (gl14-land 127 x3) 2)
        (<= 0 i)
        (<= (gl14-region x1) 0)
        (<= (gl14-region x) 0)
        (<= (gl14-region x2) 0)
        (<= 3 i)
        (gl14-linked-p)
        (gl14-is-uint16-p i)
        (gl14-valid-rw-p a 1)
        (gl14-valid-rw-p a2 1)
        (gl14-is-uint8-p x3)
        (gl14-bit-test-p x3 7)
        (gl14-valid-rd-p a3 1)
        (implies
         (< 0 i)
         (gl14-valid-rd-p a3 i)))
       (gl14-valid-rd-p (gl14-shift a1 2) 1))))))

(value-triple :itpeval-statement-checked)

:q
