;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_Sub_subqtvc: the multiprecision subtraction
;; verification condition for possibly different operand lengths, borrow
;; arithmetic, alias-separated limb arrays, and preservation of pointer data
;; and metadata.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Fixed-width words are represented exactly by canonical unsigned integers.
;; Signed 32-bit observations use two's-complement interpretation.

(defun mpsub-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mpsub-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun mpsub-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mpsub-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Array data has an independent natural length and a total limb map on all
;; mathematical integers. Pointer, zone, and alias-memory carriers remain
;; arbitrary inhabited source types.

(defstub mpsub-data-p (data) t)
(defstub mpsub-data-length (data) t)
(defstub mpsub-data-elt (data index) t)
(defstub mpsub-pointer-p (pointer) t)
(defstub mpsub-zone-p (zone) t)
(defstub mpsub-memory-p (memory) t)

(defstub mpsub-data (pointer) t)
(defstub mpsub-offset (pointer) t)
(defstub mpsub-minimum (pointer) t)
(defstub mpsub-maximum (pointer) t)
(defstub mpsub-writable (pointer) t)
(defstub mpsub-zone (pointer) t)

(defstub mpsub-zr (memory) t)
(defstub mpsub-zx (memory) t)
(defstub mpsub-zy (memory) t)
(defstub mpsub-mr (memory) t)
(defstub mpsub-mx (memory) t)
(defstub mpsub-my (memory) t)
(defstub mpsub-lr (memory) t)
(defstub mpsub-lx (memory) t)
(defstub mpsub-ly (memory) t)
(defstub mpsub-ok (memory) t)

(defun-sk mpsub-data-domain-nonempty-p ()
  (exists (data)
    (mpsub-data-p data)))

(defun-sk mpsub-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mpsub-pointer-p pointer)))

(defun-sk mpsub-zone-domain-nonempty-p ()
  (exists (zone)
    (mpsub-zone-p zone)))

(defun-sk mpsub-memory-domain-nonempty-p ()
  (exists (memory)
    (mpsub-memory-p memory)))

(defun-sk mpsub-data-interface-typed-p ()
  (forall (data index)
    (implies
     (mpsub-data-p data)
     (and
      (natp
       (mpsub-data-length data))
      (implies
       (integerp index)
       (mpsub-bv64-p
        (mpsub-data-elt data index)))))))

(defun-sk mpsub-pointer-interface-typed-p ()
  (forall (pointer)
    (implies
     (mpsub-pointer-p pointer)
     (and
      (mpsub-data-p
       (mpsub-data pointer))
      (integerp
       (mpsub-offset pointer))
      (integerp
       (mpsub-minimum pointer))
      (integerp
       (mpsub-maximum pointer))
      (booleanp
       (mpsub-writable pointer))
      (mpsub-zone-p
       (mpsub-zone pointer))))))

(defun-sk mpsub-memory-interface-typed-p ()
  (forall (memory)
    (implies
     (mpsub-memory-p memory)
     (and
      (mpsub-zone-p
       (mpsub-zr memory))
      (mpsub-zone-p
       (mpsub-zx memory))
      (mpsub-zone-p
       (mpsub-zy memory))
      (mpsub-bv32-p
       (mpsub-mr memory))
      (mpsub-bv32-p
       (mpsub-mx memory))
      (mpsub-bv32-p
       (mpsub-my memory))
      (mpsub-bv32-p
       (mpsub-lr memory))
      (mpsub-bv32-p
       (mpsub-lx memory))
      (mpsub-bv32-p
       (mpsub-ly memory))
      (booleanp
       (mpsub-ok memory))))))

(defun mpsub-interface-p ()
  (and
   (mpsub-data-domain-nonempty-p)
   (mpsub-pointer-domain-nonempty-p)
   (mpsub-zone-domain-nonempty-p)
   (mpsub-memory-domain-nonempty-p)
   (mpsub-data-interface-typed-p)
   (mpsub-pointer-interface-typed-p)
   (mpsub-memory-interface-typed-p)))

;; Source array equality is equality of the independent length and of the
;; arbitrary total integer-indexed element map.

(defun-sk mpsub-data-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpsub-data-elt left index)
      (mpsub-data-elt right index)))))

(defun mpsub-array-equal-p (left right)
  (and
   (equal
    (mpsub-data-length left)
    (mpsub-data-length right))
   (mpsub-data-equal-p left right)))

(defun mpsub-pelt (pointer index)
  (mpsub-data-elt
   (mpsub-data pointer)
   index))

(defun mpsub-plength (pointer)
  (mpsub-data-length
   (mpsub-data pointer)))

;; Little-endian radix-2^64 interpretation on the source half-open interval.

(defun mpsub-value-from (data index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+
     (mpsub-data-elt data index)
     (*
      18446744073709551616
      (mpsub-value-from
       data
       (+ index 1)
       (- count 1))))))

(defun mpsub-value (pointer size)
  (mpsub-value-from
   (mpsub-data pointer)
   (mpsub-offset pointer)
   (nfix size)))

(defun mpsub-radix-power (exponent)
  (expt
   18446744073709551616
   (nfix exponent)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpsub-valid-p (pointer size)
  (and
   (mpsub-pointer-p pointer)
   (mpsub-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0
       (mpsub-minimum pointer))
   (<= (mpsub-minimum pointer)
       (mpsub-offset pointer))
   (<= (+ (mpsub-offset pointer)
          size)
       (mpsub-maximum pointer))
   (<= (mpsub-maximum pointer)
       (mpsub-plength pointer))))

(defun mpsub-view-p (current old)
  (and
   (equal
    (mpsub-offset current)
    (mpsub-offset old))
   (equal
    (mpsub-writable current)
    (mpsub-writable old))
   (equal
    (mpsub-zone current)
    (mpsub-zone old))))

(defun mpsub-view-with-minimum-p (current old)
  (and
   (mpsub-view-p current old)
   (equal
    (mpsub-minimum current)
    (mpsub-minimum old))))

(defun-sk mpsub-pelts-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpsub-pelt left index)
      (mpsub-pelt right index)))))

(defun-sk mpsub-map-eq-sub-shift-p
    (left right left-start right-start size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index size))
      (equal
       (mpsub-pelt
        left
        (+ left-start index))
       (mpsub-pelt
        right
        (+ right-start index)))))))

(defun-sk mpsub-map-eq-sub-p
    (left right lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (mpsub-pelt left index)
       (mpsub-pelt right index))))))

(defun-sk mpsub-outside-equal-p
    (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index
          (mpsub-offset new))
       (<= (+ (mpsub-offset new)
              size)
           index))
      (equal
       (mpsub-pelt new index)
       (mpsub-pelt old index))))))

(defun mpsub-result-alias-safe-p
    (result operand result-size operand-size)
  (or
   (equal
    (mpsub-offset result)
    (mpsub-offset operand))
   (<= (+ (mpsub-offset result)
          result-size)
       (mpsub-offset operand))
   (<= (+ (mpsub-offset operand)
          operand-size)
       (mpsub-offset result))))

(defun mpsub-memory-view-p (current old)
  (and
   (equal (mpsub-zr current)
          (mpsub-zr old))
   (equal (mpsub-zx current)
          (mpsub-zx old))
   (equal (mpsub-zy current)
          (mpsub-zy old))
   (equal (mpsub-mr current)
          (mpsub-mr old))
   (equal (mpsub-mx current)
          (mpsub-mx old))
   (equal (mpsub-my current)
          (mpsub-my old))
   (equal (mpsub-lr current)
          (mpsub-lr old))
   (equal (mpsub-lx current)
          (mpsub-lx old))
   (equal (mpsub-ly current)
          (mpsub-ly old))))

;; The final close transition and the required postcondition.

(defun mpsub-final-transition-hyp-p
    (sx-word sy-word m1 r1 x1 y1 nr1 nx1 ny1
             nr2 nx2 ny2 r2 x2 y2)
  (let ((sx
         (mpsub-signed32 sx-word))
        (sy
         (mpsub-signed32 sy-word)))
    (and
     (equal
      (mpsub-maximum r2)
      (mpsub-signed32
       (mpsub-mr m1)))
     (equal
      (mpsub-maximum x2)
      (mpsub-signed32
       (mpsub-mx m1)))
     (equal
      (mpsub-maximum y2)
      (mpsub-signed32
       (mpsub-my m1)))
     (mpsub-map-eq-sub-shift-p
      nr1 r2
      (mpsub-offset nr2)
      (mpsub-offset r2)
      sx)
     (mpsub-map-eq-sub-shift-p
      nx1 x2
      (mpsub-offset nx2)
      (mpsub-offset x2)
      sx)
     (mpsub-map-eq-sub-shift-p
      ny1 y2
      (mpsub-offset ny2)
      (mpsub-offset y2)
      sy)
     (mpsub-outside-equal-p
      r2 r1 sx)
     (mpsub-outside-equal-p
      x2 x1 sx)
     (mpsub-outside-equal-p
      y2 y1 sy)
     (equal
      (mpsub-plength r2)
      (mpsub-plength r1))
     (equal
      (mpsub-plength x2)
      (mpsub-plength x1))
     (equal
      (mpsub-plength y2)
      (mpsub-plength y1))
     (equal
      (mpsub-minimum r2)
      (mpsub-minimum r1))
     (equal
      (mpsub-minimum x2)
      (mpsub-minimum x1))
     (equal
      (mpsub-minimum y2)
      (mpsub-minimum y1)))))

(defun mpsub-final-postcondition-p
    (sx-word sy-word r x y res r2 x2 y2)
  (let ((sx
         (mpsub-signed32 sx-word))
        (sy
         (mpsub-signed32 sy-word)))
    (and
     (equal
      (-
       (mpsub-value r2 sx)
       (*
        (mpsub-radix-power sx)
        res))
      (-
       (mpsub-value x sx)
       (mpsub-value y sy)))
     (<= 0 res)
     (<= res 1)
     (mpsub-outside-equal-p
      r2 r sx)
     (mpsub-pelts-equal-p
      x2 x)
     (mpsub-pelts-equal-p
      y2 y)
     (equal
      (mpsub-value x2 sx)
      (mpsub-value x sx))
     (equal
      (mpsub-value y2 sy)
      (mpsub-value y sy))
     (equal
      (mpsub-minimum x2)
      (mpsub-minimum x))
     (equal
      (mpsub-maximum x2)
      (mpsub-maximum x))
     (equal
      (mpsub-plength x2)
      (mpsub-plength x))
     (equal
      (mpsub-minimum y2)
      (mpsub-minimum y))
     (equal
      (mpsub-maximum y2)
      (mpsub-maximum y))
     (equal
      (mpsub-plength y2)
      (mpsub-plength y))
     (equal
      (mpsub-minimum r2)
      (mpsub-minimum r))
     (equal
      (mpsub-maximum r2)
      (mpsub-maximum r))
     (equal
      (mpsub-plength r2)
      (mpsub-plength r)))))

(defun mpsub-final-state-body-p
    (sx-word sy-word r x y r1 x1 y1 res m
             nr1 nx1 ny1
             m1 ny2 nx2 nr2 y2 x2 r2)
  (implies
   (mpsub-memory-view-p m1 m)
   (implies
    (mpsub-view-p ny2 ny1)
    (implies
     (mpsub-view-p nx2 nx1)
     (implies
      (mpsub-view-p nr2 nr1)
      (implies
       (mpsub-view-with-minimum-p y2 y1)
       (implies
        (mpsub-view-with-minimum-p x2 x1)
        (implies
         (mpsub-view-with-minimum-p r2 r1)
         (implies
          (mpsub-final-transition-hyp-p
           sx-word sy-word m1 r1 x1 y1 nr1 nx1 ny1
           nr2 nx2 ny2 r2 x2 y2)
          (mpsub-final-postcondition-p
           sx-word sy-word r x y res r2 x2 y2))))))))))

(defun-sk mpsub-all-final-states-p
    (sx-word sy-word r x y r1 x1 y1 res m
             nr1 nx1 ny1)
  (forall (m1 ny2 nx2 nr2 y2 x2 r2)
    (implies
     (and
      (mpsub-memory-p m1)
      (mpsub-pointer-p ny2)
      (mpsub-pointer-p nx2)
      (mpsub-pointer-p nr2)
      (mpsub-pointer-p y2)
      (mpsub-pointer-p x2)
      (mpsub-pointer-p r2))
     (mpsub-final-state-body-p
      sx-word sy-word r x y r1 x1 y1 res m
      nr1 nx1 ny1
      m1 ny2 nx2 nr2 y2 x2 r2))))

;; The subtraction-call postcondition and the precondition for closing the
;; alias-separated memory representation.

(defun mpsub-call-postcondition-p
    (sx-word sy-word nr nx ny nr1 nx1 ny1 res)
  (let ((sx
         (mpsub-signed32 sx-word))
        (sy
         (mpsub-signed32 sy-word)))
    (and
     (equal
      (-
       (mpsub-value nr1 sx)
       (*
        (mpsub-radix-power sx)
        res))
      (-
       (mpsub-value nx sx)
       (mpsub-value ny sy)))
     (<= 0 res)
     (<= res 1)
     (mpsub-outside-equal-p
      nr1 nr sx)
     (or
      (equal
       (mpsub-offset nr1)
       (mpsub-offset nx1))
      (mpsub-map-eq-sub-p
       nx1 nx
       (mpsub-offset nx1)
       (+ (mpsub-offset nx1)
          sx)))
     (or
      (equal
       (mpsub-offset nr1)
       (mpsub-offset ny1))
      (mpsub-map-eq-sub-p
       ny1 ny
       (mpsub-offset ny1)
       (+ (mpsub-offset ny1)
          sy))))))

(defun mpsub-close-precondition-p
    (sx-word sy-word r1 x1 y1 nr1 nx1 ny1 m)
  (let ((sx
         (mpsub-signed32 sx-word))
        (sy
         (mpsub-signed32 sy-word)))
    (and
     (equal
      (mpsub-ok m)
      t)
     (<= 0 sy)
     (<= sy sx)
     (equal
      (mpsub-zr m)
      (mpsub-zone r1))
     (equal
      (mpsub-zx m)
      (mpsub-zone x1))
     (equal
      (mpsub-zy m)
      (mpsub-zone y1))
     (equal
      (mpsub-lr m)
      sx-word)
     (equal
      (mpsub-lx m)
      sx-word)
     (equal
      (mpsub-ly m)
      sy-word)
     (<= 0
         (mpsub-offset nr1))
     (<= (+ (mpsub-offset nr1)
            sx)
         (mpsub-offset nx1))
     (<= (+ (mpsub-offset nx1)
            sx)
         (mpsub-offset ny1))
     (equal
      (mpsub-writable r1)
      t)
     (equal
      (mpsub-writable nr1)
      t))))

(defun mpsub-result-body-p
    (sx-word sy-word r x y r1 x1 y1
             nr nx ny m nr1 nx1 ny1 res)
  (implies
   (mpsub-call-postcondition-p
    sx-word sy-word nr nx ny nr1 nx1 ny1 res)
   (and
    (mpsub-close-precondition-p
     sx-word sy-word r1 x1 y1 nr1 nx1 ny1 m)
    (mpsub-all-final-states-p
     sx-word sy-word r x y r1 x1 y1 res m
     nr1 nx1 ny1))))

(defun-sk mpsub-all-results-p
    (sx-word sy-word r x y r1 x1 y1
             nr nx ny m nr1 nx1 ny1)
  (forall (res)
    (implies
     (mpsub-bv64-p res)
     (mpsub-result-body-p
      sx-word sy-word r x y r1 x1 y1
      nr nx ny m nr1 nx1 ny1 res))))

;; Pointer copies introduced around the subtraction call.

(defun mpsub-ny1-copy-hyp-p (ny1 nr1 ny)
  (and
   (mpsub-array-equal-p
    (mpsub-data ny1)
    (mpsub-data nr1))
   (equal
    (mpsub-plength nr1)
    (mpsub-plength ny))
   (equal
    (mpsub-offset ny1)
    (mpsub-offset ny))
   (equal
    (mpsub-minimum ny1)
    (mpsub-minimum ny))
   (equal
    (mpsub-maximum ny1)
    (mpsub-maximum ny))
   (equal
    (mpsub-writable ny1)
    (mpsub-writable ny))
   (equal
    (mpsub-zone ny1)
    (mpsub-zone ny))))

(defun mpsub-nx1-copy-hyp-p (nx1 nr1 nx)
  (and
   (mpsub-array-equal-p
    (mpsub-data nx1)
    (mpsub-data nr1))
   (equal
    (mpsub-plength nr1)
    (mpsub-plength nx))
   (equal
    (mpsub-offset nx1)
    (mpsub-offset nx))
   (equal
    (mpsub-minimum nx1)
    (mpsub-minimum nx))
   (equal
    (mpsub-maximum nx1)
    (mpsub-maximum nx))
   (equal
    (mpsub-writable nx1)
    (mpsub-writable nx))
   (equal
    (mpsub-zone nx1)
    (mpsub-zone nx))))

(defun mpsub-nr1-copy-hyp-p (nr1 nr)
  (and
   (equal
    (mpsub-plength nr1)
    (mpsub-plength nr))
   (equal
    (mpsub-offset nr1)
    (mpsub-offset nr))
   (equal
    (mpsub-minimum nr1)
    (mpsub-minimum nr))
   (equal
    (mpsub-maximum nr1)
    (mpsub-maximum nr))
   (equal
    (mpsub-writable nr1)
    (mpsub-writable nr))
   (equal
    (mpsub-zone nr1)
    (mpsub-zone nr))))

(defun mpsub-copied-state-body-p
    (sx-word sy-word r x y r1 x1 y1
             nr nx ny m ny1 nx1 nr1)
  (implies
   (mpsub-ny1-copy-hyp-p
    ny1 nr1 ny)
   (implies
    (mpsub-nx1-copy-hyp-p
     nx1 nr1 nx)
    (implies
     (mpsub-nr1-copy-hyp-p
      nr1 nr)
     (mpsub-all-results-p
      sx-word sy-word r x y r1 x1 y1
      nr nx ny m nr1 nx1 ny1)))))

(defun-sk mpsub-all-copied-states-p
    (sx-word sy-word r x y r1 x1 y1 nr nx ny m)
  (forall (ny1 nx1 nr1)
    (implies
     (and
      (mpsub-pointer-p ny1)
      (mpsub-pointer-p nx1)
      (mpsub-pointer-p nr1))
     (mpsub-copied-state-body-p
      sx-word sy-word r x y r1 x1 y1
      nr nx ny m ny1 nx1 nr1))))

;; State produced by opening the alias representation and the subtraction
;; routine's required precondition.

(defun mpsub-open-state-hyp-p
    (sx-word sy-word r x y r1 x1 y1 nr nx ny m)
  (let ((sx
         (mpsub-signed32 sx-word))
        (sy
         (mpsub-signed32 sy-word)))
    (and
     (equal
      (mpsub-writable nr)
      t)
     (equal
      (mpsub-value nx sx)
      (mpsub-value x sx))
     (equal
      (mpsub-value ny sy)
      (mpsub-value y sy))
     (mpsub-valid-p nr sx)
     (mpsub-valid-p nx sx)
     (mpsub-valid-p ny sy)
     (<= 0
         (mpsub-offset nr))
     (<= (+ (mpsub-offset nr)
            sx)
         (mpsub-offset nx))
     (<= (+ (mpsub-offset nx)
            sx)
         (mpsub-offset ny))
     (equal
      (mpsub-zr m)
      (mpsub-zone r1))
     (equal
      (mpsub-zx m)
      (mpsub-zone x1))
     (equal
      (mpsub-zy m)
      (mpsub-zone y1))
     (equal
      (mpsub-signed32
       (mpsub-mr m))
      (mpsub-maximum r))
     (equal
      (mpsub-signed32
       (mpsub-mx m))
      (mpsub-maximum x))
     (equal
      (mpsub-signed32
       (mpsub-my m))
      (mpsub-maximum y))
     (equal
      (mpsub-lr m)
      sx-word)
     (equal
      (mpsub-lx m)
      sx-word)
     (equal
      (mpsub-ly m)
      sy-word)
     (equal
      (mpsub-ok m)
      t)
     (mpsub-map-eq-sub-shift-p
      nr r1
      (mpsub-offset nr)
      (mpsub-offset r1)
      sx)
     (mpsub-map-eq-sub-shift-p
      nx x1
      (mpsub-offset nx)
      (mpsub-offset x1)
      sx)
     (mpsub-map-eq-sub-shift-p
      ny y1
      (mpsub-offset ny)
      (mpsub-offset y1)
      sy)
     (mpsub-pelts-equal-p
      r1 r)
     (mpsub-pelts-equal-p
      x1 x)
     (mpsub-pelts-equal-p
      y1 y)
     (equal
      (mpsub-plength r1)
      (mpsub-plength r))
     (equal
      (mpsub-plength x1)
      (mpsub-plength x))
     (equal
      (mpsub-plength y1)
      (mpsub-plength y))
     (equal
      (mpsub-minimum r1)
      (mpsub-minimum r))
     (equal
      (mpsub-minimum x1)
      (mpsub-minimum x))
     (equal
      (mpsub-minimum y1)
      (mpsub-minimum y))
     (mpsub-array-equal-p
      (mpsub-data nr)
      (mpsub-data nx))
     (mpsub-array-equal-p
      (mpsub-data nx)
      (mpsub-data ny)))))

(defun mpsub-subtraction-precondition-p
    (sx-word sy-word nr nx ny)
  (let ((sx
         (mpsub-signed32 sx-word))
        (sy
         (mpsub-signed32 sy-word)))
    (and
     (<= 0 sy)
     (<= sy sx)
     (mpsub-valid-p nr sx)
     (mpsub-valid-p nx sx)
     (mpsub-valid-p ny sy)
     (mpsub-result-alias-safe-p
      nr nx sx sx)
     (mpsub-result-alias-safe-p
      nr ny sx sy)
     (mpsub-array-equal-p
      (mpsub-data nr)
      (mpsub-data nx))
     (mpsub-array-equal-p
      (mpsub-data nx)
      (mpsub-data ny))
     (equal
      (mpsub-writable nr)
      t))))

(defun mpsub-open-state-body-p
    (sx-word sy-word r x y r1 x1 y1 nr nx ny m)
  (implies
   (mpsub-open-state-hyp-p
    sx-word sy-word r x y r1 x1 y1 nr nx ny m)
   (and
    (mpsub-subtraction-precondition-p
     sx-word sy-word nr nx ny)
    (mpsub-all-copied-states-p
     sx-word sy-word r x y r1 x1 y1 nr nx ny m))))

(defun-sk mpsub-all-open-states-p
    (sx-word sy-word r x y r1 x1 y1)
  (forall (nr nx ny m)
    (implies
     (and
      (mpsub-pointer-p nr)
      (mpsub-pointer-p nx)
      (mpsub-pointer-p ny)
      (mpsub-memory-p m))
     (mpsub-open-state-body-p
      sx-word sy-word r x y r1 x1 y1 nr nx ny m))))

(defun mpsub-initial-copy-body-p
    (sx-word sy-word r x y y1 x1 r1)
  (implies
   (mpsub-view-p y1 y)
   (implies
    (mpsub-view-p x1 x)
    (implies
     (mpsub-view-p r1 r)
     (mpsub-all-open-states-p
      sx-word sy-word r x y r1 x1 y1)))))

(defun-sk mpsub-all-initial-copies-p
    (sx-word sy-word r x y)
  (forall (y1 x1 r1)
    (implies
     (and
      (mpsub-pointer-p y1)
      (mpsub-pointer-p x1)
      (mpsub-pointer-p r1))
     (mpsub-initial-copy-body-p
      sx-word sy-word r x y y1 x1 r1))))

(defun-sk
    ntp4vc-pearl-multiprecision-sub-sub-subqtvc-statement
    ()
  (forall (sy-word sx-word r x y)
    (implies
     (and
      (mpsub-interface-p)
      (mpsub-bv32-p sy-word)
      (mpsub-bv32-p sx-word)
      (mpsub-pointer-p r)
      (mpsub-pointer-p x)
      (mpsub-pointer-p y)
      (<= 0
          (mpsub-signed32 sy-word))
      (<= (mpsub-signed32 sy-word)
          (mpsub-signed32 sx-word))
      (mpsub-valid-p
       r
       (mpsub-signed32 sx-word))
      (mpsub-valid-p
       x
       (mpsub-signed32 sx-word))
      (mpsub-valid-p
       y
       (mpsub-signed32 sy-word))
      (equal
       (mpsub-writable r)
       t))
     (and
      (mpsub-valid-p
       r
       (mpsub-signed32 sx-word))
      (mpsub-valid-p
       x
       (mpsub-signed32 sx-word))
      (mpsub-valid-p
       y
       (mpsub-signed32 sy-word))
      (equal
       (mpsub-writable r)
       t)
      (<= 0
          (mpsub-signed32 sy-word))
      (<= (mpsub-signed32 sy-word)
          (mpsub-signed32 sx-word))
      (mpsub-all-initial-copies-p
       sx-word sy-word r x y)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
