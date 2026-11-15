;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/incremental_Ce_int32_dummy_updateqtvc: the dummy-update verification
;; condition for signed interpretations of 32-bit words, signed-32 bounds,
;; and nested universally quantified output constraints. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^32 are in bijection with 32-bit words.  The signed
;; interpretation is exactly the source's two's-complement BitVec.toInt.

(defun dummy-update-bv32-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 4294967296)))

(defun dummy-update-sint32 (word)
  (if (< word 2147483648)
      word
    (- word 4294967296)))

(defun dummy-update-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Preserve the source's inner universal quantifier over every 32-bit o2.

(defun-sk dummy-update-all-o2-p (o1)
  (forall (o2)
    (implies
     (dummy-update-bv32-p o2)
     (implies
      (equal
       (dummy-update-sint32 o2)
       (+ (dummy-update-sint32 o1)
          (dummy-update-sint32 o1)))
      (equal
       (dummy-update-sint32 o2)
       42)))))

;; Preserve the source's outer universal quantifier over every 32-bit o1,
;; including the conjunction nested under the signed-value premise.

(defun-sk dummy-update-all-o1-p ()
  (forall (o1)
    (implies
     (dummy-update-bv32-p o1)
     (implies
      (equal (dummy-update-sint32 o1) 42)
      (and
       (dummy-update-int32-in-bounds-p
        (+ (dummy-update-sint32 o1)
           (dummy-update-sint32 o1)))
       (dummy-update-all-o2-p o1))))))

(defun
    ntp4vc-pearl-incremental-ce-int32-dummy-updateqtvc-statement
    (r)
  (implies
   (and
    (dummy-update-bv32-p r)
    (equal (dummy-update-sint32 r) 22))
   (and
    (dummy-update-int32-in-bounds-p 42)
    (dummy-update-all-o1-p))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
