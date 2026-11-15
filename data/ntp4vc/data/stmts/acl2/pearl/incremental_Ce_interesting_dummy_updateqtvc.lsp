;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/incremental_Ce_interesting_dummy_updateqtvc: the dummy-update
;; verification condition for signed interpretations of 32-bit words,
;; signed-32 bounds, and nested universally quantified output constraints.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^32 are in bijection with 32-bit words. The signed
;; interpretation is exactly the source's two's-complement signed value.

(defun interesting-dummy-update-bv32-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 4294967296)))

(defun interesting-dummy-update-sint32 (word)
  (if (< word 2147483648)
      word
    (- word 4294967296)))

(defun interesting-dummy-update-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Preserve the inner universal quantifier over every 32-bit output o2.

(defun-sk interesting-dummy-update-all-o2-p (o1)
  (forall (o2)
    (implies
     (interesting-dummy-update-bv32-p o2)
     (implies
      (equal
       (interesting-dummy-update-sint32 o2)
       (+ (interesting-dummy-update-sint32 o1)
          (interesting-dummy-update-sint32 o1)))
      (<= (interesting-dummy-update-sint32 o2)
          42)))))

;; Preserve the outer universal quantifier over every 32-bit output o1.

(defun-sk interesting-dummy-update-all-o1-p ()
  (forall (o1)
    (implies
     (interesting-dummy-update-bv32-p o1)
     (implies
      (equal (interesting-dummy-update-sint32 o1) 42)
      (and
       (interesting-dummy-update-int32-in-bounds-p
        (+ (interesting-dummy-update-sint32 o1)
           (interesting-dummy-update-sint32 o1)))
       (interesting-dummy-update-all-o2-p o1))))))

(defun
    ntp4vc-pearl-incremental-ce-interesting-dummy-updateqtvc-statement
    (r)
  (implies
   (and
    (interesting-dummy-update-bv32-p r)
    (< 22 (interesting-dummy-update-sint32 r)))
   (and
    (interesting-dummy-update-int32-in-bounds-p 42)
    (interesting-dummy-update-all-o1-p))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
