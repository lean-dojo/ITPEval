;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/rightmostbittrick_Rmbt_rightmost_bit_trickqtvc: the 64-bit
;; rightmost-set-bit verification condition for the expression x AND (-x).
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^64 are in bijection with the source's 64-bit words.

(defun rmbt-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value (expt 2 64))))

;; These are the source's fixed-width two's-complement negation and bitwise
;; conjunction on unsigned 64-bit representatives.

(defun rmbt-bv64-neg (value)
  (mod (- value) (expt 2 64)))

(defun rmbt-bv64-and (left right)
  (mod (logand left right) (expt 2 64)))

;; Equality of LENGTH consecutive bits beginning at START.  Modular extraction
;; is definitionally equivalent to equality of the source bit-vector slices;
;; length zero denotes the empty slice.

(defun rmbt-eq-sub-p (left right start length)
  (and
   (natp start)
   (natp length)
   (equal
    (mod
     (floor left (expt 2 start))
     (expt 2 length))
    (mod
     (floor right (expt 2 start))
     (expt 2 length)))))

;; Preserve the source universal quantifier over every 64-bit candidate
;; position returned by the ghost rightmost-position computation.

(defun-sk rmbt-all-positions-p (x)
  (forall (p-bv)
    (implies
     (rmbt-bv64-p p-bv)
     (implies
      (and
       (< p-bv 64)
       (rmbt-eq-sub-p x 0 0 p-bv)
       (logbitp p-bv x))
      (let ((r
             (rmbt-bv64-and
              x
              (rmbt-bv64-neg x))))
        (and
         (<= 0 p-bv)
         (< p-bv 64)
         (rmbt-eq-sub-p x 0 0 p-bv)
         (logbitp p-bv x)
         (rmbt-eq-sub-p r 0 0 p-bv)
         (rmbt-eq-sub-p
          r 0 (+ p-bv 1) (- 63 p-bv))
         (logbitp p-bv r)))))))

(defun
    ntp4vc-pearl-rightmostbittrick-rmbt-rightmost-bit-trickqtvc-statement
    (x)
  (implies
   (and
    (rmbt-bv64-p x)
    (not (equal x 0)))
   (and
    (not (equal x 0))
    (rmbt-all-positions-p x))))

(value-triple :itpeval-statement-checked)
:q
