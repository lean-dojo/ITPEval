;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/x509_parser/_parse_arc_Why3_ide_VC_parse_arc_assert_rte_mem_access_part1_goal5:
;; one-byte readability at a shifted parser address under the stated integer
;; bounds, allocation validity, linking, region, and bit-prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun pag5-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun pag5-address-base (address)
  (car address))

(defun pag5-address-offset (address)
  (cdr address))

(defun pag5-shift (address amount)
  (cons
   (pag5-address-base address)
   (+ (pag5-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; allocation map t and byte memory t_1, together with the source region
;; function and the linked predicate specialized to t.

(defstub pag5-allocation (index) t)
(defstub pag5-byte-memory (address) t)
(defstub pag5-region (base) t)
(defstub pag5-linked-op () t)

(defun-sk pag5-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (pag5-address-p address)
      (integerp (pag5-byte-memory address)))
     (implies
      (integerp index)
      (integerp (pag5-allocation index)))
     (implies
      (integerp base)
      (integerp (pag5-region base))))))

(defun pag5-linked-p ()
  (if (pag5-linked-op) t nil))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun pag5-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Cbits.lsl and Cbits.bit_test are mathematical integer left shift and
;; two's-complement bit testing. Both uses of lsl in this VC have
;; nonnegative shift counts.

(defun pag5-lsl (value count)
  (if (and (integerp value) (integerp count))
      (ash value count)
    0))

(defun pag5-bit-test-p (value position)
  (and
   (integerp value)
   (integerp position)
   (<= 0 position)
   (logbitp position value)))

(defun pag5-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun pag5-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

;; Exact unfoldings of Memory.valid_rw and Memory.valid_rd for t.

(defun pag5-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (pag5-address-base address))
    (<= 0 (pag5-address-offset address))
    (<=
     (+ (pag5-address-offset address) length)
     (pag5-allocation (pag5-address-base address))))))

(defun pag5-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (pag5-address-base address)))
    (<= 0 (pag5-address-offset address))
    (<=
     (+ (pag5-address-offset address) length)
     (pag5-allocation (pag5-address-base address))))))

;; Preserve the source universal condition over every mathematical integer
;; index i_3 from zero (inclusive) to i (exclusive).

(defun-sk pag5-bit-seven-prefix-p (a1 i)
  (forall (i3)
    (implies
     (integerp i3)
     (implies
      (<= 0 i3)
      (implies
       (< i3 i)
       (pag5-bit-test-p
        (pag5-byte-memory (pag5-shift a1 i3))
        7))))))

(defun-sk
    ntp4vc-parse-arc-assert-rte-mem-access-part1-goal5-statement ()
  (forall
   (a1 a a2 i1 i i2)
   (implies
    (and
     (pag5-function-types-p)
     (pag5-address-p a1)
     (pag5-address-p a)
     (pag5-address-p a2)
     (integerp i1)
     (integerp i)
     (integerp i2))
    (let
        ((x (pag5-address-base a1))
         (x1 (pag5-address-base a))
         (x2 (pag5-address-base a2)))
      (implies
       (and
        (not (equal i1 0))
        (not (equal a2 a))
        (not (equal (cons 0 0) a1))
        (not (equal x x1))
        (not (equal x2 x))
        (<= 0 i)
        (<= 0 i1)
        (<= (pag5-region x1) 0)
        (<= (pag5-region x) 0)
        (<= (pag5-region x2) 0)
        (<
         i2
         (pag5-lsl 1 (pag5-to-uint32 (* 7 i))))
        (<= i 3)
        (<= i 4)
        (<= 5 i1)
        (<= (pag5-lsl i2 7) 4294967295)
        (pag5-linked-p)
        (pag5-is-uint16-p i)
        (pag5-is-uint16-p i1)
        (pag5-is-uint32-p i2)
        (pag5-valid-rw-p a 1)
        (pag5-valid-rw-p a2 1)
        (implies
         (< 0 i1)
         (pag5-valid-rd-p (pag5-shift a1 0) i1))
        (pag5-bit-seven-prefix-p a1 i))
       (pag5-valid-rd-p (pag5-shift a1 i) 1))))))

(value-triple :itpeval-statement-checked)

:q
