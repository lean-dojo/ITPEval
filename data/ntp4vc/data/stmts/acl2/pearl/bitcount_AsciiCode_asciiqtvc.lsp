;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bitcount_AsciiCode_asciiqtvc: the 32-bit ASCII-code verification
;; condition relating a population count, a shifted mask bit, preservation of
;; the low 31 bits, and even parity. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 natural numbers below 2^32 are in bijection with source 32-bit words.

(defun asciiqtvc-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value (expt 2 32))))

;; Count exactly the low BITS bits.  At BITS = 32 this is the source
;; count_logic, whose nth_closure tests each bit in the interval [0,32).

(defun asciiqtvc-count-low-bits (value bits)
  (declare (xargs :measure (nfix bits)))
  (if (zp bits)
      0
    (+ (if (logbitp (- bits 1) value) 1 0)
       (asciiqtvc-count-low-bits value (- bits 1)))))

(defun asciiqtvc-count-logic (value)
  (asciiqtvc-count-low-bits value 32))

;; Bit-vector left shift truncates modulo 2^32.

(defun asciiqtvc-shift-left-31 (value)
  (mod (* value (expt 2 31))
       (expt 2 32)))

(defun asciiqtvc-or32 (left right)
  (mod (logior left right)
       (expt 2 32)))

;; Equality of the source extractLsb slices starting at zero with length 31.

(defun asciiqtvc-low-31-equal-p (left right)
  (equal (mod left (expt 2 31))
         (mod right (expt 2 31))))

(defun ntp4vc-pearl-bitcount-asciicode-asciiqtvc-statement (b c)
  (implies
   (and
    (asciiqtvc-bv32-p b)
    (asciiqtvc-bv32-p c)
    (not (logbitp 31 b))
    (equal c (asciiqtvc-count-logic b)))
   (and
    (or (< 31 32)
        (< 31 32))
    (let ((maskbit (asciiqtvc-shift-left-31 c)))
      (implies
       (equal maskbit (asciiqtvc-shift-left-31 c))
       (let ((code (asciiqtvc-or32 b maskbit)))
         (and
          (asciiqtvc-low-31-equal-p code b)
          (equal (mod (asciiqtvc-count-logic code) 2)
                 0))))))))

(value-triple :itpeval-statement-checked)
:q
