;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/base_info_BaseInfo_wmpn_limb_size_in_base_2qtvc:
;; the verification condition that a positive 64-bit limb lies between the
;; consecutive powers of two determined by its leading-zero count, including
;; the fixed-width conversion and range side conditions. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^n are in bijection with unsigned n-bit words.

(defun limb-size-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun limb-size-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Exact two's-complement signed interpretation of a 32-bit word.

(defun limb-size-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

;; The source UInt64.in_bounds predicate on mathematical integers.

(defun limb-size-uint64-in-bounds-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (<= value 18446744073709551615)))

;; Preserve the innermost universal quantifier over every 64-bit result word.

(defun-sk limb-size-all-results-p (u shift)
  (forall (r)
    (implies
     (limb-size-bv64-p r)
     (implies
      (equal r (- 64 shift))
      (and
       (and
        (<= 1 r)
        (<= r 64))
       (<= (expt 2 (- r 1)) u)
       (< u (expt 2 r)))))))

;; Preserve the universal conversion from the signed 32-bit count to a
;; 64-bit unsigned shift, including its explicit subtraction range check.

(defun-sk limb-size-all-shifts-p (u signed-count)
  (forall (shift)
    (implies
     (limb-size-bv64-p shift)
     (implies
      (equal shift signed-count)
      (and
       (limb-size-uint64-in-bounds-p
        (- 64 shift))
       (limb-size-all-results-p u shift))))))

;; This is the source characterization of the leading-zero count: scaling u
;; by 2^count reaches the top 64-bit interval, while one further factor of two
;; exceeds it. The count remains universally quantified over all 32-bit words.

(defun-sk limb-size-all-leading-zero-counts-p (u)
  (forall (o1)
    (implies
     (limb-size-bv32-p o1)
     (let ((signed-count
            (limb-size-signed32 o1)))
       (implies
        (and
         (<=
          (* (expt 2 signed-count) u)
          18446744073709551615)
         (<
          18446744073709551615
          (* 2 (expt 2 signed-count) u))
         (<= 0 signed-count)
         (< signed-count 64))
        (and
         (<= 0 signed-count)
         (limb-size-all-shifts-p
          u signed-count)))))))

(defun
    ntp4vc-pearl-multiprecision-base-info-baseinfo-wmpn-limb-size-in-base-2qtvc-statement
    (u)
  (implies
   (and
    (limb-size-bv64-p u)
    (< 0 u))
   (and
    (< 0 u)
    (limb-size-all-leading-zero-counts-p u))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
