;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_Sub_sub_n_rxqtvc: the verification condition for
;; in-place equal-length multiprecision subtraction, including borrow
;; arithmetic, pointer aliasing, memory framing, and metadata preservation.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Fixed-width words are represented exactly by their canonical unsigned
;; integers, with two's-complement interpretation where the source uses sint.

(defun mpsubrx-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mpsubrx-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun mpsubrx-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mpsubrx-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

(defun mpsubrx-bv64-list-p (values)
  (if (consp values)
      (and
       (mpsubrx-bv64-p (car values))
       (mpsubrx-bv64-list-p (cdr values)))
    (equal values nil)))

;; Pointer, zone, and memory-state carriers remain arbitrary inhabited source
;; types.  The conservative stubs expose precisely the observations occurring
;; in the VC; the interface predicates state every typing condition explicitly.

(defstub mpsubrx-pointer-p (pointer) t)
(defstub mpsubrx-zone-p (zone) t)
(defstub mpsubrx-memory-p (memory) t)

(defstub mpsubrx-data (pointer) t)
(defstub mpsubrx-offset (pointer) t)
(defstub mpsubrx-minimum (pointer) t)
(defstub mpsubrx-maximum (pointer) t)
(defstub mpsubrx-writable (pointer) t)
(defstub mpsubrx-zone (pointer) t)

(defstub mpsubrx-zr (memory) t)
(defstub mpsubrx-zx (memory) t)
(defstub mpsubrx-zy (memory) t)
(defstub mpsubrx-mr (memory) t)
(defstub mpsubrx-mx (memory) t)
(defstub mpsubrx-my (memory) t)
(defstub mpsubrx-lr (memory) t)
(defstub mpsubrx-lx (memory) t)
(defstub mpsubrx-ly (memory) t)
(defstub mpsubrx-ok (memory) t)

(defun-sk mpsubrx-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mpsubrx-pointer-p pointer)))

(defun-sk mpsubrx-zone-domain-nonempty-p ()
  (exists (zone)
    (mpsubrx-zone-p zone)))

(defun-sk mpsubrx-memory-domain-nonempty-p ()
  (exists (memory)
    (mpsubrx-memory-p memory)))

(defun-sk mpsubrx-pointer-interface-typed-p ()
  (forall (pointer)
    (implies
     (mpsubrx-pointer-p pointer)
     (and
      (mpsubrx-bv64-list-p
       (mpsubrx-data pointer))
      (integerp
       (mpsubrx-offset pointer))
      (integerp
       (mpsubrx-minimum pointer))
      (integerp
       (mpsubrx-maximum pointer))
      (booleanp
       (mpsubrx-writable pointer))
      (mpsubrx-zone-p
       (mpsubrx-zone pointer))))))

(defun-sk mpsubrx-memory-interface-typed-p ()
  (forall (memory)
    (implies
     (mpsubrx-memory-p memory)
     (and
      (mpsubrx-zone-p
       (mpsubrx-zr memory))
      (mpsubrx-zone-p
       (mpsubrx-zx memory))
      (mpsubrx-zone-p
       (mpsubrx-zy memory))
      (mpsubrx-bv32-p
       (mpsubrx-mr memory))
      (mpsubrx-bv32-p
       (mpsubrx-mx memory))
      (mpsubrx-bv32-p
       (mpsubrx-my memory))
      (mpsubrx-bv32-p
       (mpsubrx-lr memory))
      (mpsubrx-bv32-p
       (mpsubrx-lx memory))
      (mpsubrx-bv32-p
       (mpsubrx-ly memory))
      (booleanp
       (mpsubrx-ok memory))))))

(defun mpsubrx-interface-p ()
  (and
   (mpsubrx-pointer-domain-nonempty-p)
   (mpsubrx-zone-domain-nonempty-p)
   (mpsubrx-memory-domain-nonempty-p)
   (mpsubrx-pointer-interface-typed-p)
   (mpsubrx-memory-interface-typed-p)))

;; Int.toNat followed by total list indexing, whose default 64-bit word is 0.

(defun mpsubrx-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun mpsubrx-pelt (pointer index)
  (let* ((natural-index
          (mpsubrx-int-to-nat index))
         (values
          (mpsubrx-data pointer))
         (value
          (nth natural-index values)))
    (if (mpsubrx-bv64-p value)
        value
      0)))

;; Little-endian radix-2^64 interpretation used by the source value function.

(defun mpsubrx-value-from (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+
     (mpsubrx-pelt pointer index)
     (*
      18446744073709551616
      (mpsubrx-value-from
       pointer
       (+ index 1)
       (- count 1))))))

(defun mpsubrx-value (pointer size)
  (mpsubrx-value-from
   pointer
   (mpsubrx-offset pointer)
   (mpsubrx-int-to-nat size)))

(defun mpsubrx-radix-power (exponent)
  (expt
   18446744073709551616
   (mpsubrx-int-to-nat exponent)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpsubrx-valid-p (pointer size)
  (and
   (mpsubrx-pointer-p pointer)
   (mpsubrx-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0
       (mpsubrx-minimum pointer))
   (<= (mpsubrx-minimum pointer)
       (mpsubrx-offset pointer))
   (<= (+ (mpsubrx-offset pointer)
          size)
       (mpsubrx-maximum pointer))
   (<= (mpsubrx-maximum pointer)
       (len (mpsubrx-data pointer)))))

(defun mpsubrx-identical-p (left right)
  (and
   (equal
    (mpsubrx-data left)
    (mpsubrx-data right))
   (equal
    (mpsubrx-offset left)
    (mpsubrx-offset right))
   (equal
    (mpsubrx-minimum left)
    (mpsubrx-minimum right))
   (equal
    (mpsubrx-maximum left)
    (mpsubrx-maximum right))
   (equal
    (mpsubrx-zone left)
    (mpsubrx-zone right))))

;; Extensional equality of the source integer-indexed pelts functions.

(defun-sk mpsubrx-pelts-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpsubrx-pelt left index)
      (mpsubrx-pelt right index)))))

(defun-sk mpsubrx-map-eq-sub-shift-p
    (left right left-start right-start size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index size))
      (equal
       (mpsubrx-pelt
        left
        (+ left-start index))
       (mpsubrx-pelt
        right
        (+ right-start index)))))))

(defun-sk mpsubrx-map-eq-sub-p
    (left right lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (mpsubrx-pelt left index)
       (mpsubrx-pelt right index))))))

(defun-sk mpsubrx-outside-equal-p
    (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index
          (mpsubrx-offset new))
       (<= (+ (mpsubrx-offset new)
              size)
           index))
      (equal
       (mpsubrx-pelt new index)
       (mpsubrx-pelt old index))))))

(defun mpsubrx-separated-p (left right size)
  (or
   (and
    (<= 0
        (mpsubrx-offset left))
    (<= (+ (mpsubrx-offset left)
           size)
        (mpsubrx-offset right)))
   (and
    (<= 0
        (mpsubrx-offset right))
    (<= (+ (mpsubrx-offset right)
           size)
        (mpsubrx-offset left)))))

(defun mpsubrx-result-alias-safe-p (result operand size)
  (or
   (equal
    (mpsubrx-offset result)
    (mpsubrx-offset operand))
   (<= (+ (mpsubrx-offset result)
          size)
       (mpsubrx-offset operand))
   (<= (+ (mpsubrx-offset operand)
          size)
       (mpsubrx-offset result))))

;; Final close_rx state and postcondition.

(defun mpsubrx-final-transition-hyp-p
    (size-word m1 y1 x1 ny1 nx1
               ny2 nx2 y2 x2)
  (let ((size
         (mpsubrx-signed32 size-word)))
    (and
     (equal (mpsubrx-maximum x2)
            (mpsubrx-signed32
             (mpsubrx-mx m1)))
     (equal (mpsubrx-maximum y2)
            (mpsubrx-signed32
             (mpsubrx-my m1)))
     (mpsubrx-map-eq-sub-shift-p
      nx1 x2
      (mpsubrx-offset nx2)
      (mpsubrx-offset x2)
      size)
     (mpsubrx-map-eq-sub-shift-p
      ny1 y2
      (mpsubrx-offset ny2)
      (mpsubrx-offset y2)
      size)
     (mpsubrx-outside-equal-p
      x2 x1 size)
     (mpsubrx-outside-equal-p
      y2 y1 size)
     (equal
      (len (mpsubrx-data x2))
      (len (mpsubrx-data x1)))
     (equal
      (len (mpsubrx-data y2))
      (len (mpsubrx-data y1)))
     (equal
      (mpsubrx-minimum x2)
      (mpsubrx-minimum x1))
     (equal
      (mpsubrx-minimum y2)
      (mpsubrx-minimum y1)))))

(defun mpsubrx-final-postcondition-p
    (size-word x y res x2 y2)
  (let ((size
         (mpsubrx-signed32 size-word)))
    (and
     (equal
      (-
       (mpsubrx-value x2 size)
       (*
        (mpsubrx-radix-power size)
        res))
      (-
       (mpsubrx-value x size)
       (mpsubrx-value y size)))
     (<= 0 res)
     (<= res 1)
     (mpsubrx-outside-equal-p
      x2 x size)
     (mpsubrx-pelts-equal-p
      y2 y)
     (equal
      (mpsubrx-value y2 size)
      (mpsubrx-value y size))
     (equal
      (mpsubrx-minimum x2)
      (mpsubrx-minimum x))
     (equal
      (mpsubrx-maximum x2)
      (mpsubrx-maximum x))
     (equal
      (len (mpsubrx-data x2))
      (len (mpsubrx-data x)))
     (equal
      (mpsubrx-minimum y2)
      (mpsubrx-minimum y))
     (equal
      (mpsubrx-maximum y2)
      (mpsubrx-maximum y))
     (equal
      (len (mpsubrx-data y2))
      (len (mpsubrx-data y))))))

(defun mpsubrx-final-state-body-p
    (size-word x y x1 y1 res m ny1 nx1
               m1 ny2 nx2 y2 x2)
  (implies
   (and
    (equal (mpsubrx-zr m1)
           (mpsubrx-zr m))
    (equal (mpsubrx-zx m1)
           (mpsubrx-zx m))
    (equal (mpsubrx-zy m1)
           (mpsubrx-zy m))
    (equal (mpsubrx-mr m1)
           (mpsubrx-mr m))
    (equal (mpsubrx-mx m1)
           (mpsubrx-mx m))
    (equal (mpsubrx-my m1)
           (mpsubrx-my m))
    (equal (mpsubrx-lr m1)
           (mpsubrx-lr m))
    (equal (mpsubrx-lx m1)
           (mpsubrx-lx m))
    (equal (mpsubrx-ly m1)
           (mpsubrx-ly m)))
   (implies
    (and
     (equal (mpsubrx-offset ny2)
            (mpsubrx-offset ny1))
     (equal (mpsubrx-writable ny2)
            (mpsubrx-writable ny1))
     (equal (mpsubrx-zone ny2)
            (mpsubrx-zone ny1)))
    (implies
     (and
      (equal (mpsubrx-offset nx2)
             (mpsubrx-offset nx1))
      (equal (mpsubrx-writable nx2)
             (mpsubrx-writable nx1))
      (equal (mpsubrx-zone nx2)
             (mpsubrx-zone nx1)))
     (implies
      (and
       (equal (mpsubrx-offset y2)
              (mpsubrx-offset y1))
       (equal (mpsubrx-minimum y2)
              (mpsubrx-minimum y1))
       (equal (mpsubrx-writable y2)
              (mpsubrx-writable y1))
       (equal (mpsubrx-zone y2)
              (mpsubrx-zone y1)))
      (implies
       (and
        (equal (mpsubrx-offset x2)
               (mpsubrx-offset x1))
        (equal (mpsubrx-minimum x2)
               (mpsubrx-minimum x1))
        (equal (mpsubrx-writable x2)
               (mpsubrx-writable x1))
        (equal (mpsubrx-zone x2)
               (mpsubrx-zone x1)))
       (implies
        (mpsubrx-final-transition-hyp-p
         size-word m1 y1 x1 ny1 nx1
         ny2 nx2 y2 x2)
        (mpsubrx-final-postcondition-p
         size-word x y res x2 y2))))))))

(defun-sk mpsubrx-all-final-states-p
    (size-word x y x1 y1 res m ny1 nx1)
  (forall (m1 ny2 nx2 y2 x2)
    (implies
     (and
      (mpsubrx-memory-p m1)
      (mpsubrx-pointer-p ny2)
      (mpsubrx-pointer-p nx2)
      (mpsubrx-pointer-p y2)
      (mpsubrx-pointer-p x2))
     (mpsubrx-final-state-body-p
      size-word x y x1 y1 res m ny1 nx1
      m1 ny2 nx2 y2 x2))))

;; Postcondition of wmpn_sub_n and the continuation into close_rx.

(defun mpsubrx-call-postcondition-p
    (size-word nr nx ny nr1 nx1 ny1 res)
  (let ((size
         (mpsubrx-signed32 size-word)))
    (and
     (equal
      (-
       (mpsubrx-value nr1 size)
       (*
        (mpsubrx-radix-power size)
        res))
      (-
       (mpsubrx-value nx size)
       (mpsubrx-value ny size)))
     (<= 0 res)
     (<= res 1)
     (mpsubrx-outside-equal-p
      nr1 nr size)
     (or
      (equal
       (mpsubrx-offset nr1)
       (mpsubrx-offset nx1))
      (mpsubrx-map-eq-sub-p
       nx1 nx
       (mpsubrx-offset nx1)
       (+ (mpsubrx-offset nx1)
          size)))
     (or
      (equal
       (mpsubrx-offset nr1)
       (mpsubrx-offset ny1))
      (mpsubrx-map-eq-sub-p
       ny1 ny
       (mpsubrx-offset ny1)
       (+ (mpsubrx-offset ny1)
          size))))))

(defun mpsubrx-close-rx-precondition-p
    (size-word x1 y1 nr1 nx1 ny1 m)
  (let ((size
         (mpsubrx-signed32 size-word)))
    (and
     (equal
      (mpsubrx-writable x1)
      t)
     (equal
      (mpsubrx-writable nr1)
      t)
     (equal
      (mpsubrx-ok m)
      t)
     (<= 0 size)
     (<= size size)
     (mpsubrx-identical-p
      nr1 nx1)
     (mpsubrx-separated-p
      nx1 ny1 size)
     (equal
      (mpsubrx-zx m)
      (mpsubrx-zone x1))
     (equal
      (mpsubrx-zy m)
      (mpsubrx-zone y1))
     (equal
      (mpsubrx-lx m)
      size-word)
     (equal
      (mpsubrx-ly m)
      size-word))))

(defun mpsubrx-result-body-p
    (size-word x y x1 y1
               nr nx ny m nr1 nx1 ny1 res)
  (implies
   (mpsubrx-call-postcondition-p
    size-word nr nx ny nr1 nx1 ny1 res)
   (and
    (mpsubrx-close-rx-precondition-p
     size-word x1 y1 nr1 nx1 ny1 m)
    (mpsubrx-all-final-states-p
     size-word x y x1 y1 res m ny1 nx1))))

(defun-sk mpsubrx-all-results-p
    (size-word x y x1 y1
               nr nx ny m nr1 nx1 ny1)
  (forall (res)
    (implies
     (mpsubrx-bv64-p res)
     (mpsubrx-result-body-p
      size-word x y x1 y1
      nr nx ny m nr1 nx1 ny1 res))))

;; Copies introduced around the call to wmpn_sub_n.

(defun mpsubrx-ny1-copy-hyp-p (ny1 nr1 ny)
  (and
   (equal
    (mpsubrx-data ny1)
    (mpsubrx-data nr1))
   (equal
    (len (mpsubrx-data nr1))
    (len (mpsubrx-data ny)))
   (equal
    (mpsubrx-offset ny1)
    (mpsubrx-offset ny))
   (equal
    (mpsubrx-minimum ny1)
    (mpsubrx-minimum ny))
   (equal
    (mpsubrx-maximum ny1)
    (mpsubrx-maximum ny))
   (equal
    (mpsubrx-writable ny1)
    (mpsubrx-writable ny))
   (equal
    (mpsubrx-zone ny1)
    (mpsubrx-zone ny))))

(defun mpsubrx-nx1-copy-hyp-p (nx1 nr1 nx)
  (and
   (equal
    (mpsubrx-data nx1)
    (mpsubrx-data nr1))
   (equal
    (len (mpsubrx-data nr1))
    (len (mpsubrx-data nx)))
   (equal
    (mpsubrx-offset nx1)
    (mpsubrx-offset nx))
   (equal
    (mpsubrx-minimum nx1)
    (mpsubrx-minimum nx))
   (equal
    (mpsubrx-maximum nx1)
    (mpsubrx-maximum nx))
   (equal
    (mpsubrx-writable nx1)
    (mpsubrx-writable nx))
   (equal
    (mpsubrx-zone nx1)
    (mpsubrx-zone nx))))

(defun mpsubrx-nr1-copy-hyp-p (nr1 nr)
  (and
   (equal
    (len (mpsubrx-data nr1))
    (len (mpsubrx-data nr)))
   (equal
    (mpsubrx-offset nr1)
    (mpsubrx-offset nr))
   (equal
    (mpsubrx-minimum nr1)
    (mpsubrx-minimum nr))
   (equal
    (mpsubrx-maximum nr1)
    (mpsubrx-maximum nr))
   (equal
    (mpsubrx-writable nr1)
    (mpsubrx-writable nr))
   (equal
    (mpsubrx-zone nr1)
    (mpsubrx-zone nr))))

(defun mpsubrx-copied-state-body-p
    (size-word x y x1 y1
               nr nx ny m ny1 nx1 nr1)
  (implies
   (mpsubrx-ny1-copy-hyp-p
    ny1 nr1 ny)
   (implies
    (mpsubrx-nx1-copy-hyp-p
     nx1 nr1 nx)
    (implies
     (mpsubrx-nr1-copy-hyp-p
      nr1 nr)
     (mpsubrx-all-results-p
      size-word x y x1 y1
      nr nx ny m nr1 nx1 ny1)))))

(defun-sk mpsubrx-all-copied-states-p
    (size-word x y x1 y1 nr nx ny m)
  (forall (ny1 nx1 nr1)
    (implies
     (and
      (mpsubrx-pointer-p ny1)
      (mpsubrx-pointer-p nx1)
      (mpsubrx-pointer-p nr1))
     (mpsubrx-copied-state-body-p
      size-word x y x1 y1
      nr nx ny m ny1 nx1 nr1))))

;; State produced by open_rx and the precondition for wmpn_sub_n.

(defun mpsubrx-open-state-hyp-p
    (size-word x y x1 y1 nr nx ny m)
  (let ((size
         (mpsubrx-signed32 size-word)))
    (and
     (equal
      (mpsubrx-writable nr)
      t)
     (equal
      (mpsubrx-value nx size)
      (mpsubrx-value x size))
     (equal
      (mpsubrx-value ny size)
      (mpsubrx-value y size))
     (mpsubrx-valid-p nx size)
     (mpsubrx-valid-p ny size)
     (mpsubrx-identical-p nr nx)
     (mpsubrx-separated-p nx ny size)
     (equal
      (mpsubrx-zx m)
      (mpsubrx-zone x1))
     (equal
      (mpsubrx-zy m)
      (mpsubrx-zone y1))
     (equal
      (mpsubrx-signed32
       (mpsubrx-mx m))
      (mpsubrx-maximum x))
     (equal
      (mpsubrx-signed32
       (mpsubrx-my m))
      (mpsubrx-maximum y))
     (equal
      (mpsubrx-lx m)
      size-word)
     (equal
      (mpsubrx-ly m)
      size-word)
     (equal
      (mpsubrx-ok m)
      t)
     (mpsubrx-map-eq-sub-shift-p
      nx x1
      (mpsubrx-offset nx)
      (mpsubrx-offset x1)
      size)
     (mpsubrx-map-eq-sub-shift-p
      ny y1
      (mpsubrx-offset ny)
      (mpsubrx-offset y1)
      size)
     (mpsubrx-pelts-equal-p
      x1 x)
     (mpsubrx-pelts-equal-p
      y1 y)
     (equal
      (len (mpsubrx-data x1))
      (len (mpsubrx-data x)))
     (equal
      (len (mpsubrx-data y1))
      (len (mpsubrx-data y)))
     (equal
      (mpsubrx-minimum x1)
      (mpsubrx-minimum x))
     (equal
      (mpsubrx-minimum y1)
      (mpsubrx-minimum y))
     (equal
      (mpsubrx-data nr)
      (mpsubrx-data nx))
     (equal
      (mpsubrx-data nx)
      (mpsubrx-data ny)))))

(defun mpsubrx-wmpn-precondition-p
    (size-word nr nx ny)
  (let ((size
         (mpsubrx-signed32 size-word)))
    (and
     (<= 0 size)
     (mpsubrx-valid-p nr size)
     (mpsubrx-valid-p nx size)
     (mpsubrx-valid-p ny size)
     (mpsubrx-result-alias-safe-p
      nr nx size)
     (mpsubrx-result-alias-safe-p
      nr ny size)
     (equal
      (mpsubrx-data nr)
      (mpsubrx-data nx))
     (equal
      (mpsubrx-data nx)
      (mpsubrx-data ny))
     (equal
      (mpsubrx-writable nr)
      t))))

(defun mpsubrx-open-state-body-p
    (size-word x y x1 y1 nr nx ny m)
  (implies
   (mpsubrx-open-state-hyp-p
    size-word x y x1 y1 nr nx ny m)
   (and
    (mpsubrx-wmpn-precondition-p
     size-word nr nx ny)
    (mpsubrx-all-copied-states-p
     size-word x y x1 y1 nr nx ny m))))

(defun-sk mpsubrx-all-open-states-p
    (size-word x y x1 y1)
  (forall (nr nx ny m)
    (implies
     (and
      (mpsubrx-pointer-p nr)
      (mpsubrx-pointer-p nx)
      (mpsubrx-pointer-p ny)
      (mpsubrx-memory-p m))
     (mpsubrx-open-state-body-p
      size-word x y x1 y1 nr nx ny m))))

(defun mpsubrx-initial-copy-body-p
    (size-word x y y1 x1)
  (implies
   (and
    (equal
     (mpsubrx-offset y1)
     (mpsubrx-offset y))
    (equal
     (mpsubrx-writable y1)
     (mpsubrx-writable y))
    (equal
     (mpsubrx-zone y1)
     (mpsubrx-zone y)))
   (implies
    (and
     (equal
      (mpsubrx-offset x1)
      (mpsubrx-offset x))
     (equal
      (mpsubrx-writable x1)
      (mpsubrx-writable x))
     (equal
      (mpsubrx-zone x1)
      (mpsubrx-zone x)))
    (mpsubrx-all-open-states-p
     size-word x y x1 y1))))

(defun-sk mpsubrx-all-initial-copies-p
    (size-word x y)
  (forall (y1 x1)
    (implies
     (and
      (mpsubrx-pointer-p y1)
      (mpsubrx-pointer-p x1))
     (mpsubrx-initial-copy-body-p
      size-word x y y1 x1))))

(defun-sk
    ntp4vc-pearl-multiprecision-sub-sub-sub-n-rxqtvc-statement
    ()
  (forall (size-word x y)
    (implies
     (and
      (mpsubrx-interface-p)
      (mpsubrx-bv32-p size-word)
      (mpsubrx-pointer-p x)
      (mpsubrx-pointer-p y)
      (<= 0
          (mpsubrx-signed32 size-word))
      (mpsubrx-valid-p
       x
       (mpsubrx-signed32 size-word))
      (mpsubrx-valid-p
       y
       (mpsubrx-signed32 size-word))
      (equal
       (mpsubrx-writable x)
       t))
     (and
      (mpsubrx-valid-p
       x
       (mpsubrx-signed32 size-word))
      (mpsubrx-valid-p
       y
       (mpsubrx-signed32 size-word))
      (<= 0
          (mpsubrx-signed32 size-word))
      (<= (mpsubrx-signed32 size-word)
          (mpsubrx-signed32 size-word))
      (equal
       (mpsubrx-writable x)
       t)
      (mpsubrx-all-initial-copies-p
       size-word x y)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
