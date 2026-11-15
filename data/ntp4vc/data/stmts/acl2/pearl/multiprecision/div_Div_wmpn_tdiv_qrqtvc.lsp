;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/div_Div_wmpn_tdiv_qrqtvc: the verification condition
;; for multiprecision quotient-remainder division, including allocated
;; scratch pointers and the final quotient-remainder value constraints.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^n are in bijection with the source's unsigned
;; fixed-width words. The signed interpretation of a 32-bit word is the
;; source two's-complement interpretation.

(defun tdivvc-bv32-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 4294967296)))

(defun tdivvc-bv64-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 18446744073709551616)))

(defun tdivvc-sint32 (word)
  (if (< word 2147483648)
      word
    (- word 4294967296)))

(defun tdivvc-uint32-in-bounds-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (<= value 4294967295)))

;; Pointers and zones remain arbitrary inhabited source carriers. These
;; conservative interfaces expose exactly the pointer observations used by
;; the VC; all source typing requirements are explicit below.

(defstub tdivvc-pointer-p (pointer) t)
(defstub tdivvc-zone-p (zone) t)
(defstub tdivvc-null-zone () t)
(defstub tdivvc-data (pointer) t)
(defstub tdivvc-offset (pointer) t)
(defstub tdivvc-minimum (pointer) t)
(defstub tdivvc-maximum (pointer) t)
(defstub tdivvc-writable (pointer) t)
(defstub tdivvc-zone (pointer) t)

(defun tdivvc-bv64-list-p (values)
  (if (consp values)
      (and
       (tdivvc-bv64-p (car values))
       (tdivvc-bv64-list-p (cdr values)))
    (equal values nil)))

(defun-sk tdivvc-pointer-domain-nonempty-p ()
  (exists (pointer)
    (tdivvc-pointer-p pointer)))

(defun-sk tdivvc-pointer-selectors-typed-p ()
  (forall (pointer)
    (implies
     (tdivvc-pointer-p pointer)
     (and
      (tdivvc-bv64-list-p (tdivvc-data pointer))
      (integerp (tdivvc-offset pointer))
      (integerp (tdivvc-minimum pointer))
      (integerp (tdivvc-maximum pointer))
      (booleanp (tdivvc-writable pointer))
      (tdivvc-zone-p (tdivvc-zone pointer))))))

(defun tdivvc-interface-p ()
  (and
   (tdivvc-pointer-domain-nonempty-p)
   (tdivvc-zone-p (tdivvc-null-zone))
   (tdivvc-pointer-selectors-typed-p)))

;; Int.toNat sends negative indices to zero. Total list lookup uses the
;; canonical inhabited default 64-bit word zero.

(defun tdivvc-int-to-nat (value)
  (if (and (integerp value)
           (< value 0))
      0
    (nfix value)))

(defun tdivvc-pelts (pointer index)
  (let ((word
         (nth
          (tdivvc-int-to-nat index)
          (tdivvc-data pointer))))
    (if (tdivvc-bv64-p word)
        word
      0)))

(defun tdivvc-plength (pointer)
  (len (tdivvc-data pointer)))

;; This is mach.c.C.valid after expanding its signed-32 size bound and
;; pointer interval conditions.

(defun tdivvc-valid-p (pointer size)
  (and
   (tdivvc-pointer-p pointer)
   (integerp size)
   (<= -2147483648 size)
   (<= size 2147483647)
   (<= 0 size)
   (<= 0 (tdivvc-minimum pointer))
   (<= (tdivvc-minimum pointer)
       (tdivvc-offset pointer))
   (<= (+ (tdivvc-offset pointer) size)
       (tdivvc-maximum pointer))
   (<= (tdivvc-maximum pointer)
       (tdivvc-plength pointer))))

;; Little-endian base-2^64 value of a half-open pointer interval.

(defun tdivvc-value-sub-count (pointer index count)
  (if (zp count)
      0
    (+ (tdivvc-pelts pointer index)
       (* 18446744073709551616
          (tdivvc-value-sub-count
           pointer
           (+ index 1)
           (- count 1))))))

(defun tdivvc-value (pointer size)
  (tdivvc-value-sub-count
   pointer
   (tdivvc-offset pointer)
   (nfix size)))

(defun tdivvc-is-not-null-p (pointer)
  (not
   (equal
    (tdivvc-zone pointer)
    (tdivvc-null-zone))))

(defun tdivvc-is-not-null-spec-p (pointer)
  (equal
   (tdivvc-is-not-null-p pointer)
   (not
    (equal
     (tdivvc-zone pointer)
     (tdivvc-null-zone)))))

;; The allocation premise is the exact malloc result description in the
;; exported VC. The conditional length clause is intentionally retained.

(defun tdivvc-allocation-description-p (pointer size)
  (and
   (implies
    (not
     (equal
      (tdivvc-zone pointer)
      (tdivvc-null-zone)))
    (equal (tdivvc-plength pointer) size))
   (equal (tdivvc-offset pointer) 0)
   (equal (tdivvc-minimum pointer) 0)
   (equal (tdivvc-maximum pointer)
          (tdivvc-plength pointer))
   (equal (tdivvc-writable pointer) t)))

(defun tdivvc-same-metadata-p (left right)
  (and
   (equal (tdivvc-plength left)
          (tdivvc-plength right))
   (equal (tdivvc-offset left)
          (tdivvc-offset right))
   (equal (tdivvc-minimum left)
          (tdivvc-minimum right))
   (equal (tdivvc-maximum left)
          (tdivvc-maximum right))
   (equal (tdivvc-writable left)
          (tdivvc-writable right))
   (equal (tdivvc-zone left)
          (tdivvc-zone right))))

(defun tdivvc-canonical-freed-pointer-p (pointer)
  (and
   (equal (tdivvc-offset pointer) 0)
   (equal (tdivvc-minimum pointer) 0)
   (equal (tdivvc-maximum pointer)
          (tdivvc-plength pointer))
   (equal (tdivvc-writable pointer) t)))

(defun tdivvc-division-result-p
    (sy sx x y q1 r1)
  (and
   (equal
    (tdivvc-value x (tdivvc-sint32 sx))
    (+
     (*
      (tdivvc-value
       q1
       (+ (- (tdivvc-sint32 sx)
             (tdivvc-sint32 sy))
          1))
      (tdivvc-value y (tdivvc-sint32 sy)))
     (tdivvc-value r1 (tdivvc-sint32 sy))))
   (<
    (tdivvc-value r1 (tdivvc-sint32 sy))
    (tdivvc-value y (tdivvc-sint32 sy)))))

;; Preserve the four universally quantified post-state pointers and the
;; source's right-associated chain of metadata implications.

(defun tdivvc-final-output-case-p
    (sy sx x y q r nx ny ny1 nx1 r1 q1)
  (implies
   (tdivvc-same-metadata-p ny1 ny)
   (implies
    (tdivvc-same-metadata-p nx1 nx)
    (implies
     (tdivvc-same-metadata-p r1 r)
     (implies
      (tdivvc-same-metadata-p q1 q)
      (implies
       (tdivvc-division-result-p
        sy sx x y q1 r1)
       (and
        (tdivvc-canonical-freed-pointer-p nx1)
        (tdivvc-canonical-freed-pointer-p ny1)
        (tdivvc-division-result-p
         sy sx x y q1 r1))))))))

(defun-sk tdivvc-all-final-outputs-p
    (sy sx x y q r nx ny)
  (forall (ny1 nx1 r1 q1)
    (implies
     (and
      (tdivvc-pointer-p ny1)
      (tdivvc-pointer-p nx1)
      (tdivvc-pointer-p r1)
      (tdivvc-pointer-p q1))
     (tdivvc-final-output-case-p
      sy sx x y q r nx ny ny1 nx1 r1 q1))))

(defun tdivvc-inner-precondition-p
    (sy sx x y q r nx ny)
  (and
   (and
    (<= 1 (tdivvc-sint32 sy))
    (<= (tdivvc-sint32 sy)
        (tdivvc-sint32 sx))
    (<= (tdivvc-sint32 sx)
        (- 2147483647 1)))
   (tdivvc-valid-p x (tdivvc-sint32 sx))
   (tdivvc-valid-p y (tdivvc-sint32 sy))
   (tdivvc-valid-p
    q
    (+ (- (tdivvc-sint32 sx)
          (tdivvc-sint32 sy))
       1))
   (tdivvc-valid-p r (tdivvc-sint32 sy))
   (tdivvc-valid-p
    nx
    (+ (tdivvc-sint32 sx) 1))
   (tdivvc-valid-p ny (tdivvc-sint32 sy))
   (and
    (equal (tdivvc-writable nx) t)
    (equal (tdivvc-writable ny) t))
   (<
    0
    (tdivvc-pelts
     y
     (+
      (tdivvc-offset y)
      (tdivvc-sint32 sy)
      -1)))
   (equal (tdivvc-writable q) t)
   (equal (tdivvc-writable r) t)
   (tdivvc-all-final-outputs-p
    sy sx x y q r nx ny)))

;; The following predicates preserve the source quantifier order
;; o1, o2, nx, o3, ny and every intervening implication.

(defun tdivvc-ny-case-p
    (sy sx x y q r nx o3 ny)
  (implies
   (tdivvc-allocation-description-p ny o3)
   (implies
    (tdivvc-is-not-null-spec-p ny)
    (implies
     (tdivvc-is-not-null-p ny)
     (tdivvc-inner-precondition-p
      sy sx x y q r nx ny)))))

(defun-sk tdivvc-all-ny-p
    (sy sx x y q r nx o3)
  (forall (ny)
    (implies
     (tdivvc-pointer-p ny)
     (tdivvc-ny-case-p
      sy sx x y q r nx o3 ny))))

(defun-sk tdivvc-all-o3-p
    (sy sx x y q r nx)
  (forall (o3)
    (implies
     (tdivvc-bv32-p o3)
     (implies
      (equal o3 (tdivvc-sint32 sy))
      (and
       (<= 0 o3)
       (tdivvc-all-ny-p
        sy sx x y q r nx o3))))))

(defun tdivvc-nx-case-p
    (sy sx x y q r o2 nx)
  (implies
   (tdivvc-allocation-description-p nx o2)
   (implies
    (tdivvc-is-not-null-spec-p nx)
    (implies
     (tdivvc-is-not-null-p nx)
     (and
      (<= 0 (tdivvc-sint32 sy))
      (tdivvc-all-o3-p
       sy sx x y q r nx))))))

(defun-sk tdivvc-all-nx-p
    (sy sx x y q r o2)
  (forall (nx)
    (implies
     (tdivvc-pointer-p nx)
     (tdivvc-nx-case-p
      sy sx x y q r o2 nx))))

(defun-sk tdivvc-all-o2-p
    (sy sx x y q r o1)
  (forall (o2)
    (implies
     (tdivvc-bv32-p o2)
     (implies
      (equal o2 (+ o1 1))
      (and
       (<= 0 o2)
       (tdivvc-all-nx-p
        sy sx x y q r o2))))))

(defun-sk tdivvc-all-o1-p
    (sy sx x y q r)
  (forall (o1)
    (implies
     (tdivvc-bv32-p o1)
     (implies
      (equal o1 (tdivvc-sint32 sx))
      (and
       (tdivvc-uint32-in-bounds-p
        (+ o1 1))
       (tdivvc-all-o2-p
        sy sx x y q r o1))))))

(defun
    ntp4vc-pearl-multiprecision-div-div-wmpn-tdiv-qrqtvc-statement
    (sy sx x y q r qxn)
  (implies
   (and
    (tdivvc-interface-p)
    (tdivvc-bv32-p sy)
    (tdivvc-bv32-p sx)
    (tdivvc-pointer-p x)
    (tdivvc-pointer-p y)
    (tdivvc-pointer-p q)
    (tdivvc-pointer-p r)
    (tdivvc-bv32-p qxn)
    (<= 1 (tdivvc-sint32 sy))
    (<= (tdivvc-sint32 sy)
        (tdivvc-sint32 sx))
    (<= (tdivvc-sint32 sx)
        (- 2147483647 1))
    (tdivvc-valid-p x (tdivvc-sint32 sx))
    (tdivvc-valid-p y (tdivvc-sint32 sy))
    (tdivvc-valid-p
     q
     (+ (- (tdivvc-sint32 sx)
           (tdivvc-sint32 sy))
        1))
    (tdivvc-valid-p r (tdivvc-sint32 sy))
    (equal (tdivvc-writable q) t)
    (equal (tdivvc-writable r) t)
    (equal (tdivvc-sint32 qxn) 0)
    (<
     0
     (tdivvc-pelts
      y
      (+
       (tdivvc-offset y)
       (tdivvc-sint32 sy)
       -1))))
   (and
    (<= 0 (tdivvc-sint32 sx))
    (tdivvc-all-o1-p
     sy sx x y q r))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
