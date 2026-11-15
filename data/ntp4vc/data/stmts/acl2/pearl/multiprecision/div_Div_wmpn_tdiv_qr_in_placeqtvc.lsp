;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/div_Div_wmpn_tdiv_qr_in_placeqtvc: the verification
;; condition for in-place multiprecision division, including allocated
;; scratch pointers and quotient-remainder value constraints. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^n are in bijection with the source's unsigned
;; fixed-width words. The signed interpretation of a 32-bit word is the
;; source two's-complement interpretation.

(defun ddiv-bv32-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 4294967296)))

(defun ddiv-bv64-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 18446744073709551616)))

(defun ddiv-sint32 (word)
  (if (< word 2147483648)
      word
    (- word 4294967296)))

(defun ddiv-uint32-in-bounds-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (<= value 4294967295)))

;; Pointers and zones remain arbitrary inhabited source carriers. These
;; conservative interfaces expose exactly the pointer observations used by
;; the VC; all source typing requirements are explicit below.

(defstub ddiv-pointer-p (pointer) t)
(defstub ddiv-zone-p (zone) t)
(defstub ddiv-null-zone () t)
(defstub ddiv-data (pointer) t)
(defstub ddiv-offset (pointer) t)
(defstub ddiv-minimum (pointer) t)
(defstub ddiv-maximum (pointer) t)
(defstub ddiv-writable (pointer) t)
(defstub ddiv-zone (pointer) t)

(defun ddiv-bv64-list-p (values)
  (if (consp values)
      (and
       (ddiv-bv64-p (car values))
       (ddiv-bv64-list-p (cdr values)))
    (equal values nil)))

(defun-sk ddiv-pointer-domain-nonempty-p ()
  (exists (pointer)
    (ddiv-pointer-p pointer)))

(defun-sk ddiv-pointer-selectors-typed-p ()
  (forall (pointer)
    (implies
     (ddiv-pointer-p pointer)
     (and
      (ddiv-bv64-list-p (ddiv-data pointer))
      (integerp (ddiv-offset pointer))
      (integerp (ddiv-minimum pointer))
      (integerp (ddiv-maximum pointer))
      (booleanp (ddiv-writable pointer))
      (ddiv-zone-p (ddiv-zone pointer))))))

(defun ddiv-interface-p ()
  (and
   (ddiv-pointer-domain-nonempty-p)
   (ddiv-zone-p (ddiv-null-zone))
   (ddiv-pointer-selectors-typed-p)))

;; Int.toNat sends negative indices to zero. Total list lookup uses the
;; canonical inhabited default 64-bit word zero.

(defun ddiv-int-to-nat (value)
  (if (and (integerp value)
           (< value 0))
      0
    (nfix value)))

(defun ddiv-pelts (pointer index)
  (let ((word
         (nth
          (ddiv-int-to-nat index)
          (ddiv-data pointer))))
    (if (ddiv-bv64-p word)
        word
      0)))

(defun ddiv-plength (pointer)
  (len (ddiv-data pointer)))

;; This is mach.c.C.valid after expanding its signed-32 size bound and
;; pointer interval conditions.

(defun ddiv-valid-p (pointer size)
  (and
   (ddiv-pointer-p pointer)
   (integerp size)
   (<= -2147483648 size)
   (<= size 2147483647)
   (<= 0 size)
   (<= 0 (ddiv-minimum pointer))
   (<= (ddiv-minimum pointer)
       (ddiv-offset pointer))
   (<= (+ (ddiv-offset pointer) size)
       (ddiv-maximum pointer))
   (<= (ddiv-maximum pointer)
       (ddiv-plength pointer))))

;; Little-endian base-2^64 value of a half-open pointer interval.

(defun ddiv-value-sub-count (pointer index count)
  (if (zp count)
      0
    (+ (ddiv-pelts pointer index)
       (* 18446744073709551616
          (ddiv-value-sub-count
           pointer
           (+ index 1)
           (- count 1))))))

(defun ddiv-value (pointer size)
  (ddiv-value-sub-count
   pointer
   (ddiv-offset pointer)
   (nfix size)))

(defun ddiv-is-not-null-p (pointer)
  (not
   (equal
    (ddiv-zone pointer)
    (ddiv-null-zone))))

(defun ddiv-is-not-null-spec-p (pointer)
  (equal
   (ddiv-is-not-null-p pointer)
   (not
    (equal
     (ddiv-zone pointer)
     (ddiv-null-zone)))))

;; The allocation premise is the exact malloc result description in the
;; exported VC. The conditional length clause is intentionally retained.

(defun ddiv-allocation-description-p (pointer size)
  (and
   (implies
    (not
     (equal
      (ddiv-zone pointer)
      (ddiv-null-zone)))
    (equal (ddiv-plength pointer) size))
   (equal (ddiv-offset pointer) 0)
   (equal (ddiv-minimum pointer) 0)
   (equal (ddiv-maximum pointer)
          (ddiv-plength pointer))
   (equal (ddiv-writable pointer) t)))

(defun ddiv-same-metadata-p (left right)
  (and
   (equal (ddiv-plength left)
          (ddiv-plength right))
   (equal (ddiv-offset left)
          (ddiv-offset right))
   (equal (ddiv-minimum left)
          (ddiv-minimum right))
   (equal (ddiv-maximum left)
          (ddiv-maximum right))
   (equal (ddiv-writable left)
          (ddiv-writable right))
   (equal (ddiv-zone left)
          (ddiv-zone right))))

(defun ddiv-canonical-freed-pointer-p (pointer)
  (and
   (equal (ddiv-offset pointer) 0)
   (equal (ddiv-minimum pointer) 0)
   (equal (ddiv-maximum pointer)
          (ddiv-plength pointer))
   (equal (ddiv-writable pointer) t)))

(defun ddiv-division-result-p
    (sy sx x y q1 x1)
  (and
   (equal
    (ddiv-value x (ddiv-sint32 sx))
    (+
     (*
      (ddiv-value
       q1
       (+ (- (ddiv-sint32 sx)
             (ddiv-sint32 sy))
          1))
      (ddiv-value y (ddiv-sint32 sy)))
     (ddiv-value x1 (ddiv-sint32 sy))))
   (<
    (ddiv-value x1 (ddiv-sint32 sy))
    (ddiv-value y (ddiv-sint32 sy)))))

;; Preserve the four universally quantified post-state pointers and the
;; source's right-associated chain of metadata implications.

(defun ddiv-final-output-case-p
    (sy sx x y q nx ny ny1 nx1 x1 q1)
  (implies
   (ddiv-same-metadata-p ny1 ny)
   (implies
    (ddiv-same-metadata-p nx1 nx)
    (implies
     (ddiv-same-metadata-p x1 x)
     (implies
      (ddiv-same-metadata-p q1 q)
      (implies
       (ddiv-division-result-p
        sy sx x y q1 x1)
       (and
        (ddiv-canonical-freed-pointer-p nx1)
        (ddiv-canonical-freed-pointer-p ny1)
        (ddiv-division-result-p
         sy sx x y q1 x1))))))))

(defun-sk ddiv-all-final-outputs-p
    (sy sx x y q nx ny)
  (forall (ny1 nx1 x1 q1)
    (implies
     (and
      (ddiv-pointer-p ny1)
      (ddiv-pointer-p nx1)
      (ddiv-pointer-p x1)
      (ddiv-pointer-p q1))
     (ddiv-final-output-case-p
      sy sx x y q nx ny ny1 nx1 x1 q1))))

(defun ddiv-inner-precondition-p
    (sy sx x y q nx ny)
  (and
   (and
    (<= 1 (ddiv-sint32 sy))
    (<= (ddiv-sint32 sy)
        (ddiv-sint32 sx))
    (<= (ddiv-sint32 sx)
        (- 2147483647 1)))
   (ddiv-valid-p x (ddiv-sint32 sx))
   (ddiv-valid-p y (ddiv-sint32 sy))
   (ddiv-valid-p
    q
    (+ (- (ddiv-sint32 sx)
          (ddiv-sint32 sy))
       1))
   (ddiv-valid-p
    nx
    (+ (ddiv-sint32 sx) 1))
   (ddiv-valid-p ny (ddiv-sint32 sy))
   (and
    (equal (ddiv-writable q) t)
    (equal (ddiv-writable x) t))
   (and
    (equal (ddiv-writable nx) t)
    (equal (ddiv-writable ny) t))
   (<
    0
    (ddiv-pelts
     y
     (+
      (ddiv-offset y)
      (ddiv-sint32 sy)
      -1)))
   (ddiv-all-final-outputs-p
    sy sx x y q nx ny)))

;; The following predicates preserve the source quantifier order
;; o1, o2, nx, o3, ny and every intervening implication.

(defun ddiv-ny-case-p
    (sy sx x y q nx o3 ny)
  (implies
   (ddiv-allocation-description-p ny o3)
   (implies
    (ddiv-is-not-null-spec-p ny)
    (implies
     (ddiv-is-not-null-p ny)
     (ddiv-inner-precondition-p
      sy sx x y q nx ny)))))

(defun-sk ddiv-all-ny-p
    (sy sx x y q nx o3)
  (forall (ny)
    (implies
     (ddiv-pointer-p ny)
     (ddiv-ny-case-p
      sy sx x y q nx o3 ny))))

(defun-sk ddiv-all-o3-p
    (sy sx x y q nx)
  (forall (o3)
    (implies
     (ddiv-bv32-p o3)
     (implies
      (equal o3 (ddiv-sint32 sy))
      (and
       (<= 0 o3)
       (ddiv-all-ny-p
        sy sx x y q nx o3))))))

(defun ddiv-nx-case-p
    (sy sx x y q o2 nx)
  (implies
   (ddiv-allocation-description-p nx o2)
   (implies
    (ddiv-is-not-null-spec-p nx)
    (implies
     (ddiv-is-not-null-p nx)
     (and
      (<= 0 (ddiv-sint32 sy))
      (ddiv-all-o3-p
       sy sx x y q nx))))))

(defun-sk ddiv-all-nx-p
    (sy sx x y q o2)
  (forall (nx)
    (implies
     (ddiv-pointer-p nx)
     (ddiv-nx-case-p
      sy sx x y q o2 nx))))

(defun-sk ddiv-all-o2-p
    (sy sx x y q o1)
  (forall (o2)
    (implies
     (ddiv-bv32-p o2)
     (implies
      (equal o2 (+ o1 1))
      (and
       (<= 0 o2)
       (ddiv-all-nx-p
        sy sx x y q o2))))))

(defun-sk ddiv-all-o1-p
    (sy sx x y q)
  (forall (o1)
    (implies
     (ddiv-bv32-p o1)
     (implies
      (equal o1 (ddiv-sint32 sx))
      (and
       (ddiv-uint32-in-bounds-p
        (+ o1 1))
       (ddiv-all-o2-p
        sy sx x y q o1))))))

(defun
    ntp4vc-pearl-multiprecision-div-div-wmpn-tdiv-qr-in-placeqtvc-statement
    (sy sx x y q qxn)
  (implies
   (and
    (ddiv-interface-p)
    (ddiv-bv32-p sy)
    (ddiv-bv32-p sx)
    (ddiv-pointer-p x)
    (ddiv-pointer-p y)
    (ddiv-pointer-p q)
    (ddiv-bv32-p qxn)
    (<= 1 (ddiv-sint32 sy))
    (<= (ddiv-sint32 sy)
        (ddiv-sint32 sx))
    (<= (ddiv-sint32 sx)
        (- 2147483647 1))
    (ddiv-valid-p x (ddiv-sint32 sx))
    (ddiv-valid-p y (ddiv-sint32 sy))
    (ddiv-valid-p
     q
     (+ (- (ddiv-sint32 sx)
           (ddiv-sint32 sy))
        1))
    (equal (ddiv-writable x) t)
    (equal (ddiv-writable q) t)
    (equal (ddiv-sint32 qxn) 0)
    (<
     0
     (ddiv-pelts
      y
      (+
       (ddiv-offset y)
       (ddiv-sint32 sy)
       -1))))
   (and
    (<= 0 (ddiv-sint32 sx))
    (ddiv-all-o1-p
     sy sx x y q))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
