;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/add_Add_add_ryqtvc: the verification condition for
;; adding unequal-length multiprecision integers into the second operand,
;; including carry arithmetic, pointer aliasing, memory framing, and metadata
;; preservation. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Fixed-width words are represented by their canonical unsigned integers.

(defun mpaddry-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mpaddry-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Exact two's-complement signed interpretation of a 32-bit word.

(defun mpaddry-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mpaddry-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Pointers, zones, and alias memories remain arbitrary inhabited source
;; carrier types. Conservative stubs expose exactly the observations used by
;; the VC, and the interface predicates state every source typing condition.

(defstub mpaddry-pointer-p (pointer) t)
(defstub mpaddry-zone-p (zone) t)
(defstub mpaddry-data-length (pointer) t)
(defstub mpaddry-pelt (pointer index) t)
(defstub mpaddry-offset (pointer) t)
(defstub mpaddry-minimum (pointer) t)
(defstub mpaddry-maximum (pointer) t)
(defstub mpaddry-writable (pointer) t)
(defstub mpaddry-zone (pointer) t)

(defstub mpaddry-memory-p (memory) t)
(defstub mpaddry-zr (memory) t)
(defstub mpaddry-zx (memory) t)
(defstub mpaddry-zy (memory) t)
(defstub mpaddry-mr (memory) t)
(defstub mpaddry-mx (memory) t)
(defstub mpaddry-my (memory) t)
(defstub mpaddry-lr (memory) t)
(defstub mpaddry-lx (memory) t)
(defstub mpaddry-ly (memory) t)
(defstub mpaddry-ok (memory) t)

(defun-sk mpaddry-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mpaddry-pointer-p pointer)))

(defun-sk mpaddry-zone-domain-nonempty-p ()
  (exists (zone)
    (mpaddry-zone-p zone)))

(defun-sk mpaddry-memory-domain-nonempty-p ()
  (exists (memory)
    (mpaddry-memory-p memory)))

(defun-sk mpaddry-pointer-interface-typed-p ()
  (forall (pointer index)
    (implies
     (mpaddry-pointer-p pointer)
     (and
      (natp (mpaddry-data-length pointer))
      (integerp
       (mpaddry-offset pointer))
      (integerp
       (mpaddry-minimum pointer))
      (integerp
       (mpaddry-maximum pointer))
      (booleanp
       (mpaddry-writable pointer))
      (mpaddry-zone-p
       (mpaddry-zone pointer))
      (implies
       (integerp index)
       (mpaddry-bv64-p
        (mpaddry-pelt pointer index)))))))

(defun-sk mpaddry-memory-interface-typed-p ()
  (forall (memory)
    (implies
     (mpaddry-memory-p memory)
     (and
      (mpaddry-zone-p (mpaddry-zr memory))
      (mpaddry-zone-p (mpaddry-zx memory))
      (mpaddry-zone-p (mpaddry-zy memory))
      (mpaddry-bv32-p (mpaddry-mr memory))
      (mpaddry-bv32-p (mpaddry-mx memory))
      (mpaddry-bv32-p (mpaddry-my memory))
      (mpaddry-bv32-p (mpaddry-lr memory))
      (mpaddry-bv32-p (mpaddry-lx memory))
      (mpaddry-bv32-p (mpaddry-ly memory))
      (booleanp (mpaddry-ok memory))))))

(defun mpaddry-interface-p ()
  (and
   (mpaddry-pointer-domain-nonempty-p)
   (mpaddry-zone-domain-nonempty-p)
   (mpaddry-memory-domain-nonempty-p)
   (mpaddry-pointer-interface-typed-p)
   (mpaddry-memory-interface-typed-p)))

;; Int.toNat is used for source recursion counts and exponents.

(defun mpaddry-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

;; Little-endian radix-2^64 value of the indicated pointer prefix.

(defun mpaddry-value-from (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+
     (mpaddry-pelt pointer index)
     (*
      18446744073709551616
      (mpaddry-value-from
       pointer
       (+ index 1)
       (- count 1))))))

(defun mpaddry-value (pointer size)
  (mpaddry-value-from
   pointer
   (mpaddry-offset pointer)
   (mpaddry-int-to-nat size)))

(defun mpaddry-radix-power (exponent)
  (expt
   18446744073709551616
   (mpaddry-int-to-nat exponent)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpaddry-valid-p (pointer size)
  (and
   (mpaddry-pointer-p pointer)
   (mpaddry-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0
       (mpaddry-minimum pointer))
   (<= (mpaddry-minimum pointer)
       (mpaddry-offset pointer))
   (<= (+ (mpaddry-offset pointer)
          size)
       (mpaddry-maximum pointer))
   (<= (mpaddry-maximum pointer)
       (mpaddry-data-length pointer))))

;; Extensional equality and interval equality over the source's full integer
;; index domain.

(defun-sk mpaddry-same-pelts-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpaddry-pelt left index)
      (mpaddry-pelt right index)))))

(defun mpaddry-same-data-p (left right)
  (and
   (equal
    (mpaddry-data-length left)
    (mpaddry-data-length right))
   (mpaddry-same-pelts-p left right)))

(defun-sk mpaddry-map-eq-sub-p
    (left right lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (mpaddry-pelt left index)
       (mpaddry-pelt right index))))))

(defun-sk mpaddry-map-eq-sub-shift-p
    (left right left-offset right-offset size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index size))
      (equal
       (mpaddry-pelt left
                     (+ left-offset index))
       (mpaddry-pelt right
                     (+ right-offset index)))))))

(defun-sk mpaddry-frame-p (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index
          (mpaddry-offset new))
       (<= (+ (mpaddry-offset new)
              size)
           index))
      (equal
       (mpaddry-pelt new index)
       (mpaddry-pelt old index))))))

;; Why3 Alias.identical compares all pointer observations except writable.

(defun mpaddry-identical-p (left right)
  (and
   (mpaddry-same-data-p left right)
   (equal
    (mpaddry-offset left)
    (mpaddry-offset right))
   (equal
    (mpaddry-minimum left)
    (mpaddry-minimum right))
   (equal
    (mpaddry-maximum left)
    (mpaddry-maximum right))
   (equal
    (mpaddry-zone left)
    (mpaddry-zone right))))

(defun mpaddry-disjoint-same-size-p
    (left right size)
  (or
   (and
    (<= 0 (mpaddry-offset left))
    (<= (+ (mpaddry-offset left) size)
        (mpaddry-offset right)))
   (and
    (<= 0 (mpaddry-offset right))
    (<= (+ (mpaddry-offset right) size)
        (mpaddry-offset left)))))

(defun mpaddry-separated-or-equal-p
    (left right left-size right-size)
  (or
   (equal
    (mpaddry-offset left)
    (mpaddry-offset right))
   (<= (+ (mpaddry-offset left)
          left-size)
       (mpaddry-offset right))
   (<= (+ (mpaddry-offset right)
          right-size)
       (mpaddry-offset left))))

;; The final close_sep continuation.

(defun mpaddry-memory-copy-p (new old)
  (and
   (equal (mpaddry-zr new) (mpaddry-zr old))
   (equal (mpaddry-zx new) (mpaddry-zx old))
   (equal (mpaddry-zy new) (mpaddry-zy old))
   (equal (mpaddry-mr new) (mpaddry-mr old))
   (equal (mpaddry-mx new) (mpaddry-mx old))
   (equal (mpaddry-my new) (mpaddry-my old))
   (equal (mpaddry-lr new) (mpaddry-lr old))
   (equal (mpaddry-lx new) (mpaddry-lx old))
   (equal (mpaddry-ly new) (mpaddry-ly old))))

(defun mpaddry-offset-writable-zone-copy-p
    (new old)
  (and
   (equal
    (mpaddry-offset new)
    (mpaddry-offset old))
   (equal
    (mpaddry-writable new)
    (mpaddry-writable old))
   (equal
    (mpaddry-zone new)
    (mpaddry-zone old))))

(defun mpaddry-offset-min-writable-zone-copy-p
    (new old)
  (and
   (equal
    (mpaddry-offset new)
    (mpaddry-offset old))
   (equal
    (mpaddry-minimum new)
    (mpaddry-minimum old))
   (equal
    (mpaddry-writable new)
    (mpaddry-writable old))
   (equal
    (mpaddry-zone new)
    (mpaddry-zone old))))

(defun mpaddry-close-premise-p
    (sx m1 nx1 ny1 nx2 ny2 y1 x1 y2 x2)
  (let ((size (mpaddry-signed32 sx)))
    (and
     (equal
      (mpaddry-maximum y2)
      (mpaddry-signed32
       (mpaddry-mx m1)))
     (equal
      (mpaddry-maximum x2)
      (mpaddry-signed32
       (mpaddry-my m1)))
     (mpaddry-map-eq-sub-shift-p
      ny1 y2
      (mpaddry-offset ny2)
      (mpaddry-offset y2)
      size)
     (mpaddry-map-eq-sub-shift-p
      nx1 x2
      (mpaddry-offset nx2)
      (mpaddry-offset x2)
      size)
     (mpaddry-frame-p y2 y1 size)
     (mpaddry-frame-p x2 x1 size)
     (equal
      (mpaddry-data-length y2)
      (mpaddry-data-length y1))
     (equal
      (mpaddry-data-length x2)
      (mpaddry-data-length x1))
     (equal
      (mpaddry-minimum y2)
      (mpaddry-minimum y1))
     (equal
      (mpaddry-minimum x2)
      (mpaddry-minimum x1)))))

(defun mpaddry-final-postcondition-p
    (sy sx x y res x2 y2)
  (let ((short-size (mpaddry-signed32 sy))
        (size (mpaddry-signed32 sx)))
    (and
     (equal
      (+
       (mpaddry-value y2 size)
       (*
        (mpaddry-radix-power size)
        res))
      (+
       (mpaddry-value x size)
       (mpaddry-value y short-size)))
     (<= 0 res)
     (<= res 1)
     (mpaddry-frame-p y2 y size)
     (mpaddry-same-pelts-p x2 x)
     (equal
      (mpaddry-value x2 size)
      (mpaddry-value x size))
     (equal
      (mpaddry-minimum x2)
      (mpaddry-minimum x))
     (equal
      (mpaddry-maximum x2)
      (mpaddry-maximum x))
     (equal
      (mpaddry-data-length x2)
      (mpaddry-data-length x))
     (equal
      (mpaddry-minimum y2)
      (mpaddry-minimum y))
     (equal
      (mpaddry-maximum y2)
      (mpaddry-maximum y))
     (equal
      (mpaddry-data-length y2)
      (mpaddry-data-length y)))))

(defun mpaddry-final-state-body-p
    (sy sx x y res m nx1 ny1 y1 x1
        m1 nx2 ny2 y2 x2)
  (implies
   (mpaddry-memory-copy-p m1 m)
   (implies
    (mpaddry-offset-writable-zone-copy-p
     nx2 nx1)
    (implies
     (mpaddry-offset-writable-zone-copy-p
      ny2 ny1)
     (implies
      (mpaddry-offset-min-writable-zone-copy-p
       y2 y1)
      (implies
       (mpaddry-offset-min-writable-zone-copy-p
        x2 x1)
       (implies
        (mpaddry-close-premise-p
         sx m1 nx1 ny1 nx2 ny2 y1 x1 y2 x2)
        (mpaddry-final-postcondition-p
         sy sx x y res x2 y2))))))))

(defun-sk mpaddry-all-final-states-p
    (sy sx x y res m nx1 ny1 y1 x1)
  (forall (m1 nx2 ny2 y2 x2)
    (implies
     (and
      (mpaddry-memory-p m1)
      (mpaddry-pointer-p nx2)
      (mpaddry-pointer-p ny2)
      (mpaddry-pointer-p y2)
      (mpaddry-pointer-p x2))
     (mpaddry-final-state-body-p
      sy sx x y res m nx1 ny1 y1 x1
      m1 nx2 ny2 y2 x2))))

;; The postcondition immediately after wmpn_add.

(defun mpaddry-result-premise-p
    (sy sx nx ny nr nx1 ny1 nr1 res)
  (let ((short-size (mpaddry-signed32 sy))
        (size (mpaddry-signed32 sx)))
    (and
     (equal
      (+
       (mpaddry-value nr1 size)
       (*
        (mpaddry-radix-power size)
        res))
      (+
       (mpaddry-value nx size)
       (mpaddry-value ny short-size)))
     (<= 0 res)
     (<= res 1)
     (mpaddry-frame-p nr1 nr size)
     (or
      (equal
       (mpaddry-offset nr1)
       (mpaddry-offset nx1))
      (mpaddry-map-eq-sub-p
       nx1 nx
       (mpaddry-offset nx1)
       (+ (mpaddry-offset nx1)
          size)))
     (or
      (equal
       (mpaddry-offset nr1)
       (mpaddry-offset ny1))
      (mpaddry-map-eq-sub-p
       ny1 ny
       (mpaddry-offset ny1)
       (+ (mpaddry-offset ny1)
          short-size))))))

(defun mpaddry-middle-postcondition-p
    (sx y1 x1 nr1 ny1 nx1 m)
  (let ((size (mpaddry-signed32 sx)))
    (and
     (equal (mpaddry-writable y1) t)
     (equal (mpaddry-writable nr1) t)
     (equal (mpaddry-ok m) t)
     (<= 0 size)
     (<= size size)
     (mpaddry-identical-p nr1 ny1)
     (mpaddry-disjoint-same-size-p
      ny1 nx1 size)
     (equal
      (mpaddry-zx m)
      (mpaddry-zone y1))
     (equal
      (mpaddry-zy m)
      (mpaddry-zone x1))
     (equal (mpaddry-lx m) sx)
     (equal (mpaddry-ly m) sx))))

(defun mpaddry-result-body-p
    (sy sx x y nr ny nx m y1 x1
        nr1 ny1 nx1 res)
  (implies
   (mpaddry-result-premise-p
    sy sx nx ny nr nx1 ny1 nr1 res)
   (and
    (mpaddry-middle-postcondition-p
     sx y1 x1 nr1 ny1 nx1 m)
    (mpaddry-all-final-states-p
     sy sx x y res m nx1 ny1 y1 x1))))

(defun-sk mpaddry-all-results-p
    (sy sx x y nr ny nx m y1 x1
        nr1 ny1 nx1)
  (forall (res)
    (implies
     (mpaddry-bv64-p res)
     (mpaddry-result-body-p
      sy sx x y nr ny nx m y1 x1
      nr1 ny1 nx1 res))))

;; The three pointer snapshots supplied to the wmpn_add continuation.

(defun mpaddry-nx1-copy-p (nx1 nr1 nx)
  (and
   (mpaddry-same-data-p nx1 nr1)
   (equal
    (mpaddry-data-length nr1)
    (mpaddry-data-length nx))
   (equal
    (mpaddry-offset nx1)
    (mpaddry-offset nx))
   (equal
    (mpaddry-minimum nx1)
    (mpaddry-minimum nx))
   (equal
    (mpaddry-maximum nx1)
    (mpaddry-maximum nx))
   (equal
    (mpaddry-writable nx1)
    (mpaddry-writable nx))
   (equal
    (mpaddry-zone nx1)
    (mpaddry-zone nx))))

(defun mpaddry-ny1-copy-p (ny1 nr1 ny)
  (and
   (mpaddry-same-data-p ny1 nr1)
   (equal
    (mpaddry-data-length nr1)
    (mpaddry-data-length ny))
   (equal
    (mpaddry-offset ny1)
    (mpaddry-offset ny))
   (equal
    (mpaddry-minimum ny1)
    (mpaddry-minimum ny))
   (equal
    (mpaddry-maximum ny1)
    (mpaddry-maximum ny))
   (equal
    (mpaddry-writable ny1)
    (mpaddry-writable ny))
   (equal
    (mpaddry-zone ny1)
    (mpaddry-zone ny))))

(defun mpaddry-nr1-copy-p (nr1 nr)
  (and
   (equal
    (mpaddry-data-length nr1)
    (mpaddry-data-length nr))
   (equal
    (mpaddry-offset nr1)
    (mpaddry-offset nr))
   (equal
    (mpaddry-minimum nr1)
    (mpaddry-minimum nr))
   (equal
    (mpaddry-maximum nr1)
    (mpaddry-maximum nr))
   (equal
    (mpaddry-writable nr1)
    (mpaddry-writable nr))
   (equal
    (mpaddry-zone nr1)
    (mpaddry-zone nr))))

(defun mpaddry-refined-pointer-body-p
    (sy sx x y nr ny nx m y1 x1
        nx1 ny1 nr1)
  (implies
   (mpaddry-nx1-copy-p nx1 nr1 nx)
   (implies
    (mpaddry-ny1-copy-p ny1 nr1 ny)
    (implies
     (mpaddry-nr1-copy-p nr1 nr)
     (mpaddry-all-results-p
      sy sx x y nr ny nx m y1 x1
      nr1 ny1 nx1)))))

(defun-sk mpaddry-all-refined-pointers-p
    (sy sx x y nr ny nx m y1 x1)
  (forall (nx1 ny1 nr1)
    (implies
     (and
      (mpaddry-pointer-p nx1)
      (mpaddry-pointer-p ny1)
      (mpaddry-pointer-p nr1))
     (mpaddry-refined-pointer-body-p
      sy sx x y nr ny nx m y1 x1
      nx1 ny1 nr1))))

;; The open_rx continuation and its immediate source postcondition.

(defun mpaddry-open-premise-p
    (sy sx x y y1 x1 nr ny nx m)
  (declare (ignore sy))
  (let ((size (mpaddry-signed32 sx)))
    (and
     (equal (mpaddry-writable nr) t)
     (equal
      (mpaddry-value ny size)
      (mpaddry-value y size))
     (equal
      (mpaddry-value nx size)
      (mpaddry-value x size))
     (mpaddry-valid-p ny size)
     (mpaddry-valid-p nx size)
     (mpaddry-identical-p nr ny)
     (mpaddry-disjoint-same-size-p
      ny nx size)
     (equal
      (mpaddry-zx m)
      (mpaddry-zone y1))
     (equal
      (mpaddry-zy m)
      (mpaddry-zone x1))
     (equal
      (mpaddry-signed32
       (mpaddry-mx m))
      (mpaddry-maximum y))
     (equal
      (mpaddry-signed32
       (mpaddry-my m))
      (mpaddry-maximum x))
     (equal (mpaddry-lx m) sx)
     (equal (mpaddry-ly m) sx)
     (equal (mpaddry-ok m) t)
     (mpaddry-map-eq-sub-shift-p
      ny y1
      (mpaddry-offset ny)
      (mpaddry-offset y1)
      size)
     (mpaddry-map-eq-sub-shift-p
      nx x1
      (mpaddry-offset nx)
      (mpaddry-offset x1)
      size)
     (mpaddry-same-pelts-p y1 y)
     (mpaddry-same-pelts-p x1 x)
     (equal
      (mpaddry-data-length y1)
      (mpaddry-data-length y))
     (equal
      (mpaddry-data-length x1)
      (mpaddry-data-length x))
     (equal
      (mpaddry-minimum y1)
      (mpaddry-minimum y))
     (equal
      (mpaddry-minimum x1)
      (mpaddry-minimum x))
     (mpaddry-same-data-p nr ny)
     (mpaddry-same-data-p ny nx))))

(defun mpaddry-open-postcondition-p
    (sy sx nr ny nx)
  (let ((short-size (mpaddry-signed32 sy))
        (size (mpaddry-signed32 sx)))
    (and
     (<= 0 short-size)
     (<= short-size size)
     (mpaddry-valid-p nr size)
     (mpaddry-valid-p nx size)
     (mpaddry-valid-p ny short-size)
     (mpaddry-separated-or-equal-p
      nr nx size size)
     (mpaddry-separated-or-equal-p
      nr ny size short-size)
     (mpaddry-same-data-p nr nx)
     (mpaddry-same-data-p nx ny)
     (equal (mpaddry-writable nr) t))))

(defun mpaddry-open-state-body-p
    (sy sx x y y1 x1 nr ny nx m)
  (implies
   (mpaddry-open-premise-p
    sy sx x y y1 x1 nr ny nx m)
   (and
    (mpaddry-open-postcondition-p
     sy sx nr ny nx)
    (mpaddry-all-refined-pointers-p
     sy sx x y nr ny nx m y1 x1))))

(defun-sk mpaddry-all-open-states-p
    (sy sx x y y1 x1)
  (forall (nr ny nx m)
    (implies
     (and
      (mpaddry-pointer-p nr)
      (mpaddry-pointer-p ny)
      (mpaddry-pointer-p nx)
      (mpaddry-memory-p m))
     (mpaddry-open-state-body-p
      sy sx x y y1 x1 nr ny nx m))))

(defun mpaddry-y1-x1-body-p
    (sy sx x y y1 x1)
  (implies
   (mpaddry-offset-writable-zone-copy-p
    y1 y)
   (implies
    (mpaddry-offset-writable-zone-copy-p
     x1 x)
    (mpaddry-all-open-states-p
     sy sx x y y1 x1))))

(defun-sk mpaddry-all-initial-snapshots-p
    (sy sx x y)
  (forall (y1 x1)
    (implies
     (and
      (mpaddry-pointer-p y1)
      (mpaddry-pointer-p x1))
     (mpaddry-y1-x1-body-p
      sy sx x y y1 x1))))

(defun mpaddry-conclusion-p (sy sx x y)
  (let ((size (mpaddry-signed32 sx)))
    (and
     (mpaddry-valid-p y size)
     (mpaddry-valid-p x size)
     (<= 0 size)
     (<= size size)
     (equal (mpaddry-writable y) t)
     (mpaddry-all-initial-snapshots-p
      sy sx x y))))

(defun-sk
    ntp4vc-pearl-multiprecision-add-add-add-ryqtvc-statement
    ()
  (forall (sy sx x y)
    (implies
     (and
      (mpaddry-interface-p)
      (mpaddry-bv32-p sy)
      (mpaddry-bv32-p sx)
      (mpaddry-pointer-p x)
      (mpaddry-pointer-p y)
      (<= 0
          (mpaddry-signed32 sy))
      (<= (mpaddry-signed32 sy)
          (mpaddry-signed32 sx))
      (mpaddry-valid-p
       x
       (mpaddry-signed32 sx))
      (mpaddry-valid-p
       y
       (mpaddry-signed32 sx))
      (equal (mpaddry-writable y) t))
     (mpaddry-conclusion-p sy sx x y))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
