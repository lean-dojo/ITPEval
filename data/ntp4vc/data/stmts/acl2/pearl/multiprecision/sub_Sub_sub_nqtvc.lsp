;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_Sub_sub_nqtvc: the verification condition for
;; equal-length multiprecision subtraction into a separate result pointer,
;; including borrow arithmetic, aliasing, memory framing, and metadata
;; preservation. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Fixed-width words are represented exactly by their canonical unsigned
;; integers, with two's-complement interpretation where the source uses sint.

(defun mpsubn-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mpsubn-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun mpsubn-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mpsubn-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

(defun mpsubn-bv64-list-p (values)
  (if (consp values)
      (and
       (mpsubn-bv64-p (car values))
       (mpsubn-bv64-list-p (cdr values)))
    (equal values nil)))

;; Pointer, zone, and alias-memory carriers remain arbitrary inhabited source
;; types. Conservative stubs expose exactly the observations occurring in the
;; VC, while the interface predicate states every typing condition explicitly.

(defstub mpsubn-pointer-p (pointer) t)
(defstub mpsubn-zone-p (zone) t)
(defstub mpsubn-memory-p (memory) t)

(defstub mpsubn-data (pointer) t)
(defstub mpsubn-offset (pointer) t)
(defstub mpsubn-minimum (pointer) t)
(defstub mpsubn-maximum (pointer) t)
(defstub mpsubn-writable (pointer) t)
(defstub mpsubn-zone (pointer) t)

(defstub mpsubn-zr (memory) t)
(defstub mpsubn-zx (memory) t)
(defstub mpsubn-zy (memory) t)
(defstub mpsubn-mr (memory) t)
(defstub mpsubn-mx (memory) t)
(defstub mpsubn-my (memory) t)
(defstub mpsubn-lr (memory) t)
(defstub mpsubn-lx (memory) t)
(defstub mpsubn-ly (memory) t)
(defstub mpsubn-ok (memory) t)

(defun-sk mpsubn-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mpsubn-pointer-p pointer)))

(defun-sk mpsubn-zone-domain-nonempty-p ()
  (exists (zone)
    (mpsubn-zone-p zone)))

(defun-sk mpsubn-memory-domain-nonempty-p ()
  (exists (memory)
    (mpsubn-memory-p memory)))

(defun-sk mpsubn-pointer-interface-typed-p ()
  (forall (pointer)
    (implies
     (mpsubn-pointer-p pointer)
     (and
      (mpsubn-bv64-list-p
       (mpsubn-data pointer))
      (integerp
       (mpsubn-offset pointer))
      (integerp
       (mpsubn-minimum pointer))
      (integerp
       (mpsubn-maximum pointer))
      (booleanp
       (mpsubn-writable pointer))
      (mpsubn-zone-p
       (mpsubn-zone pointer))))))

(defun-sk mpsubn-memory-interface-typed-p ()
  (forall (memory)
    (implies
     (mpsubn-memory-p memory)
     (and
      (mpsubn-zone-p
       (mpsubn-zr memory))
      (mpsubn-zone-p
       (mpsubn-zx memory))
      (mpsubn-zone-p
       (mpsubn-zy memory))
      (mpsubn-bv32-p
       (mpsubn-mr memory))
      (mpsubn-bv32-p
       (mpsubn-mx memory))
      (mpsubn-bv32-p
       (mpsubn-my memory))
      (mpsubn-bv32-p
       (mpsubn-lr memory))
      (mpsubn-bv32-p
       (mpsubn-lx memory))
      (mpsubn-bv32-p
       (mpsubn-ly memory))
      (booleanp
       (mpsubn-ok memory))))))

(defun mpsubn-interface-p ()
  (and
   (mpsubn-pointer-domain-nonempty-p)
   (mpsubn-zone-domain-nonempty-p)
   (mpsubn-memory-domain-nonempty-p)
   (mpsubn-pointer-interface-typed-p)
   (mpsubn-memory-interface-typed-p)))

;; Int.toNat followed by total list indexing, whose default 64-bit word is 0.

(defun mpsubn-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun mpsubn-pelt (pointer index)
  (let* ((natural-index
          (mpsubn-int-to-nat index))
         (values
          (mpsubn-data pointer))
         (value
          (nth natural-index values)))
    (if (mpsubn-bv64-p value)
        value
      0)))

;; Little-endian radix-2^64 interpretation used by the source value function.

(defun mpsubn-value-from (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+
     (mpsubn-pelt pointer index)
     (*
      18446744073709551616
      (mpsubn-value-from
       pointer
       (+ index 1)
       (- count 1))))))

(defun mpsubn-value (pointer size)
  (mpsubn-value-from
   pointer
   (mpsubn-offset pointer)
   (mpsubn-int-to-nat size)))

(defun mpsubn-radix-power (exponent)
  (expt
   18446744073709551616
   (mpsubn-int-to-nat exponent)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpsubn-valid-p (pointer size)
  (and
   (mpsubn-pointer-p pointer)
   (mpsubn-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0
       (mpsubn-minimum pointer))
   (<= (mpsubn-minimum pointer)
       (mpsubn-offset pointer))
   (<= (+ (mpsubn-offset pointer)
          size)
       (mpsubn-maximum pointer))
   (<= (mpsubn-maximum pointer)
       (len (mpsubn-data pointer)))))

(defun mpsubn-view-p (current old)
  (and
   (equal
    (mpsubn-offset current)
    (mpsubn-offset old))
   (equal
    (mpsubn-writable current)
    (mpsubn-writable old))
   (equal
    (mpsubn-zone current)
    (mpsubn-zone old))))

(defun mpsubn-view-with-minimum-p (current old)
  (and
   (mpsubn-view-p current old)
   (equal
    (mpsubn-minimum current)
    (mpsubn-minimum old))))

(defun-sk mpsubn-pelts-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpsubn-pelt left index)
      (mpsubn-pelt right index)))))

(defun-sk mpsubn-map-eq-sub-shift-p
    (left right left-start right-start size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index size))
      (equal
       (mpsubn-pelt
        left
        (+ left-start index))
       (mpsubn-pelt
        right
        (+ right-start index)))))))

(defun-sk mpsubn-map-eq-sub-p
    (left right lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (mpsubn-pelt left index)
       (mpsubn-pelt right index))))))

(defun-sk mpsubn-outside-equal-p
    (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index
          (mpsubn-offset new))
       (<= (+ (mpsubn-offset new)
              size)
           index))
      (equal
       (mpsubn-pelt new index)
       (mpsubn-pelt old index))))))

(defun mpsubn-result-alias-safe-p (result operand size)
  (or
   (equal
    (mpsubn-offset result)
    (mpsubn-offset operand))
   (<= (+ (mpsubn-offset result)
          size)
       (mpsubn-offset operand))
   (<= (+ (mpsubn-offset operand)
          size)
       (mpsubn-offset result))))

;; Final close state and postcondition.

(defun mpsubn-memory-view-p (current old)
  (and
   (equal (mpsubn-zr current)
          (mpsubn-zr old))
   (equal (mpsubn-zx current)
          (mpsubn-zx old))
   (equal (mpsubn-zy current)
          (mpsubn-zy old))
   (equal (mpsubn-mr current)
          (mpsubn-mr old))
   (equal (mpsubn-mx current)
          (mpsubn-mx old))
   (equal (mpsubn-my current)
          (mpsubn-my old))
   (equal (mpsubn-lr current)
          (mpsubn-lr old))
   (equal (mpsubn-lx current)
          (mpsubn-lx old))
   (equal (mpsubn-ly current)
          (mpsubn-ly old))))

(defun mpsubn-final-transition-hyp-p
    (size-word m1 r1 x1 y1 nr1 nx1 ny1
               nr2 nx2 ny2 r2 x2 y2)
  (let ((size
         (mpsubn-signed32 size-word)))
    (and
     (equal
      (mpsubn-maximum r2)
      (mpsubn-signed32
       (mpsubn-mr m1)))
     (equal
      (mpsubn-maximum x2)
      (mpsubn-signed32
       (mpsubn-mx m1)))
     (equal
      (mpsubn-maximum y2)
      (mpsubn-signed32
       (mpsubn-my m1)))
     (mpsubn-map-eq-sub-shift-p
      nr1 r2
      (mpsubn-offset nr2)
      (mpsubn-offset r2)
      size)
     (mpsubn-map-eq-sub-shift-p
      nx1 x2
      (mpsubn-offset nx2)
      (mpsubn-offset x2)
      size)
     (mpsubn-map-eq-sub-shift-p
      ny1 y2
      (mpsubn-offset ny2)
      (mpsubn-offset y2)
      size)
     (mpsubn-outside-equal-p
      r2 r1 size)
     (mpsubn-outside-equal-p
      x2 x1 size)
     (mpsubn-outside-equal-p
      y2 y1 size)
     (equal
      (len (mpsubn-data r2))
      (len (mpsubn-data r1)))
     (equal
      (len (mpsubn-data x2))
      (len (mpsubn-data x1)))
     (equal
      (len (mpsubn-data y2))
      (len (mpsubn-data y1)))
     (equal
      (mpsubn-minimum r2)
      (mpsubn-minimum r1))
     (equal
      (mpsubn-minimum x2)
      (mpsubn-minimum x1))
     (equal
      (mpsubn-minimum y2)
      (mpsubn-minimum y1)))))

(defun mpsubn-final-postcondition-p
    (size-word r x y res r2 x2 y2)
  (let ((size
         (mpsubn-signed32 size-word)))
    (and
     (equal
      (-
       (mpsubn-value r2 size)
       (*
        (mpsubn-radix-power size)
        res))
      (-
       (mpsubn-value x size)
       (mpsubn-value y size)))
     (<= 0 res)
     (<= res 1)
     (mpsubn-outside-equal-p
      r2 r size)
     (mpsubn-pelts-equal-p
      x2 x)
     (mpsubn-pelts-equal-p
      y2 y)
     (equal
      (mpsubn-value x2 size)
      (mpsubn-value x size))
     (equal
      (mpsubn-value y2 size)
      (mpsubn-value y size))
     (equal
      (mpsubn-minimum x2)
      (mpsubn-minimum x))
     (equal
      (mpsubn-maximum x2)
      (mpsubn-maximum x))
     (equal
      (len (mpsubn-data x2))
      (len (mpsubn-data x)))
     (equal
      (mpsubn-minimum y2)
      (mpsubn-minimum y))
     (equal
      (mpsubn-maximum y2)
      (mpsubn-maximum y))
     (equal
      (len (mpsubn-data y2))
      (len (mpsubn-data y)))
     (equal
      (mpsubn-minimum r2)
      (mpsubn-minimum r))
     (equal
      (mpsubn-maximum r2)
      (mpsubn-maximum r))
     (equal
      (len (mpsubn-data r2))
      (len (mpsubn-data r))))))

(defun mpsubn-final-state-body-p
    (size-word r x y r1 x1 y1 res m
               nr1 nx1 ny1
               m1 ny2 nx2 nr2 y2 x2 r2)
  (implies
   (mpsubn-memory-view-p m1 m)
   (implies
    (mpsubn-view-p ny2 ny1)
    (implies
     (mpsubn-view-p nx2 nx1)
     (implies
      (mpsubn-view-p nr2 nr1)
      (implies
       (mpsubn-view-with-minimum-p y2 y1)
       (implies
        (mpsubn-view-with-minimum-p x2 x1)
        (implies
         (mpsubn-view-with-minimum-p r2 r1)
         (implies
          (mpsubn-final-transition-hyp-p
           size-word m1 r1 x1 y1 nr1 nx1 ny1
           nr2 nx2 ny2 r2 x2 y2)
          (mpsubn-final-postcondition-p
           size-word r x y res r2 x2 y2))))))))))

(defun-sk mpsubn-all-final-states-p
    (size-word r x y r1 x1 y1 res m
               nr1 nx1 ny1)
  (forall (m1 ny2 nx2 nr2 y2 x2 r2)
    (implies
     (and
      (mpsubn-memory-p m1)
      (mpsubn-pointer-p ny2)
      (mpsubn-pointer-p nx2)
      (mpsubn-pointer-p nr2)
      (mpsubn-pointer-p y2)
      (mpsubn-pointer-p x2)
      (mpsubn-pointer-p r2))
     (mpsubn-final-state-body-p
      size-word r x y r1 x1 y1 res m
      nr1 nx1 ny1
      m1 ny2 nx2 nr2 y2 x2 r2))))

;; Postcondition of wmpn_sub_n and the continuation into the close operation.

(defun mpsubn-call-postcondition-p
    (size-word nr nx ny nr1 nx1 ny1 res)
  (let ((size
         (mpsubn-signed32 size-word)))
    (and
     (equal
      (-
       (mpsubn-value nr1 size)
       (*
        (mpsubn-radix-power size)
        res))
      (-
       (mpsubn-value nx size)
       (mpsubn-value ny size)))
     (<= 0 res)
     (<= res 1)
     (mpsubn-outside-equal-p
      nr1 nr size)
     (or
      (equal
       (mpsubn-offset nr1)
       (mpsubn-offset nx1))
      (mpsubn-map-eq-sub-p
       nx1 nx
       (mpsubn-offset nx1)
       (+ (mpsubn-offset nx1)
          size)))
     (or
      (equal
       (mpsubn-offset nr1)
       (mpsubn-offset ny1))
      (mpsubn-map-eq-sub-p
       ny1 ny
       (mpsubn-offset ny1)
       (+ (mpsubn-offset ny1)
          size))))))

(defun mpsubn-close-precondition-p
    (size-word r1 x1 y1 nr1 nx1 ny1 m)
  (let ((size
         (mpsubn-signed32 size-word)))
    (and
     (equal
      (mpsubn-ok m)
      t)
     (<= 0 size)
     (<= size size)
     (equal
      (mpsubn-zr m)
      (mpsubn-zone r1))
     (equal
      (mpsubn-zx m)
      (mpsubn-zone x1))
     (equal
      (mpsubn-zy m)
      (mpsubn-zone y1))
     (equal
      (mpsubn-lr m)
      size-word)
     (equal
      (mpsubn-lx m)
      size-word)
     (equal
      (mpsubn-ly m)
      size-word)
     (<= 0
         (mpsubn-offset nr1))
     (<= (+ (mpsubn-offset nr1)
            size)
         (mpsubn-offset nx1))
     (<= (+ (mpsubn-offset nx1)
            size)
         (mpsubn-offset ny1))
     (equal
      (mpsubn-writable r1)
      t)
     (equal
      (mpsubn-writable nr1)
      t))))

(defun mpsubn-result-body-p
    (size-word r x y r1 x1 y1
               nr nx ny m nr1 nx1 ny1 res)
  (implies
   (mpsubn-call-postcondition-p
    size-word nr nx ny nr1 nx1 ny1 res)
   (and
    (mpsubn-close-precondition-p
     size-word r1 x1 y1 nr1 nx1 ny1 m)
    (mpsubn-all-final-states-p
     size-word r x y r1 x1 y1 res m
     nr1 nx1 ny1))))

(defun-sk mpsubn-all-results-p
    (size-word r x y r1 x1 y1
               nr nx ny m nr1 nx1 ny1)
  (forall (res)
    (implies
     (mpsubn-bv64-p res)
     (mpsubn-result-body-p
      size-word r x y r1 x1 y1
      nr nx ny m nr1 nx1 ny1 res))))

;; Copies introduced around the call to wmpn_sub_n.

(defun mpsubn-ny1-copy-hyp-p (ny1 nr1 ny)
  (and
   (equal
    (mpsubn-data ny1)
    (mpsubn-data nr1))
   (equal
    (len (mpsubn-data nr1))
    (len (mpsubn-data ny)))
   (equal
    (mpsubn-offset ny1)
    (mpsubn-offset ny))
   (equal
    (mpsubn-minimum ny1)
    (mpsubn-minimum ny))
   (equal
    (mpsubn-maximum ny1)
    (mpsubn-maximum ny))
   (equal
    (mpsubn-writable ny1)
    (mpsubn-writable ny))
   (equal
    (mpsubn-zone ny1)
    (mpsubn-zone ny))))

(defun mpsubn-nx1-copy-hyp-p (nx1 nr1 nx)
  (and
   (equal
    (mpsubn-data nx1)
    (mpsubn-data nr1))
   (equal
    (len (mpsubn-data nr1))
    (len (mpsubn-data nx)))
   (equal
    (mpsubn-offset nx1)
    (mpsubn-offset nx))
   (equal
    (mpsubn-minimum nx1)
    (mpsubn-minimum nx))
   (equal
    (mpsubn-maximum nx1)
    (mpsubn-maximum nx))
   (equal
    (mpsubn-writable nx1)
    (mpsubn-writable nx))
   (equal
    (mpsubn-zone nx1)
    (mpsubn-zone nx))))

(defun mpsubn-nr1-copy-hyp-p (nr1 nr)
  (and
   (equal
    (len (mpsubn-data nr1))
    (len (mpsubn-data nr)))
   (equal
    (mpsubn-offset nr1)
    (mpsubn-offset nr))
   (equal
    (mpsubn-minimum nr1)
    (mpsubn-minimum nr))
   (equal
    (mpsubn-maximum nr1)
    (mpsubn-maximum nr))
   (equal
    (mpsubn-writable nr1)
    (mpsubn-writable nr))
   (equal
    (mpsubn-zone nr1)
    (mpsubn-zone nr))))

(defun mpsubn-copied-state-body-p
    (size-word r x y r1 x1 y1
               nr nx ny m ny1 nx1 nr1)
  (implies
   (mpsubn-ny1-copy-hyp-p
    ny1 nr1 ny)
   (implies
    (mpsubn-nx1-copy-hyp-p
     nx1 nr1 nx)
    (implies
     (mpsubn-nr1-copy-hyp-p
      nr1 nr)
     (mpsubn-all-results-p
      size-word r x y r1 x1 y1
      nr nx ny m nr1 nx1 ny1)))))

(defun-sk mpsubn-all-copied-states-p
    (size-word r x y r1 x1 y1 nr nx ny m)
  (forall (ny1 nx1 nr1)
    (implies
     (and
      (mpsubn-pointer-p ny1)
      (mpsubn-pointer-p nx1)
      (mpsubn-pointer-p nr1))
     (mpsubn-copied-state-body-p
      size-word r x y r1 x1 y1
      nr nx ny m ny1 nx1 nr1))))

;; State produced by the open operation and the precondition for wmpn_sub_n.

(defun mpsubn-open-state-hyp-p
    (size-word r x y r1 x1 y1 nr nx ny m)
  (let ((size
         (mpsubn-signed32 size-word)))
    (and
     (equal
      (mpsubn-writable nr)
      t)
     (equal
      (mpsubn-value nx size)
      (mpsubn-value x size))
     (equal
      (mpsubn-value ny size)
      (mpsubn-value y size))
     (mpsubn-valid-p nr size)
     (mpsubn-valid-p nx size)
     (mpsubn-valid-p ny size)
     (<= 0
         (mpsubn-offset nr))
     (<= (+ (mpsubn-offset nr)
            size)
         (mpsubn-offset nx))
     (<= (+ (mpsubn-offset nx)
            size)
         (mpsubn-offset ny))
     (equal
      (mpsubn-zr m)
      (mpsubn-zone r1))
     (equal
      (mpsubn-zx m)
      (mpsubn-zone x1))
     (equal
      (mpsubn-zy m)
      (mpsubn-zone y1))
     (equal
      (mpsubn-signed32
       (mpsubn-mr m))
      (mpsubn-maximum r))
     (equal
      (mpsubn-signed32
       (mpsubn-mx m))
      (mpsubn-maximum x))
     (equal
      (mpsubn-signed32
       (mpsubn-my m))
      (mpsubn-maximum y))
     (equal
      (mpsubn-lr m)
      size-word)
     (equal
      (mpsubn-lx m)
      size-word)
     (equal
      (mpsubn-ly m)
      size-word)
     (equal
      (mpsubn-ok m)
      t)
     (mpsubn-map-eq-sub-shift-p
      nr r1
      (mpsubn-offset nr)
      (mpsubn-offset r1)
      size)
     (mpsubn-map-eq-sub-shift-p
      nx x1
      (mpsubn-offset nx)
      (mpsubn-offset x1)
      size)
     (mpsubn-map-eq-sub-shift-p
      ny y1
      (mpsubn-offset ny)
      (mpsubn-offset y1)
      size)
     (mpsubn-pelts-equal-p
      r1 r)
     (mpsubn-pelts-equal-p
      x1 x)
     (mpsubn-pelts-equal-p
      y1 y)
     (equal
      (len (mpsubn-data r1))
      (len (mpsubn-data r)))
     (equal
      (len (mpsubn-data x1))
      (len (mpsubn-data x)))
     (equal
      (len (mpsubn-data y1))
      (len (mpsubn-data y)))
     (equal
      (mpsubn-minimum r1)
      (mpsubn-minimum r))
     (equal
      (mpsubn-minimum x1)
      (mpsubn-minimum x))
     (equal
      (mpsubn-minimum y1)
      (mpsubn-minimum y))
     (equal
      (mpsubn-data nr)
      (mpsubn-data nx))
     (equal
      (mpsubn-data nx)
      (mpsubn-data ny)))))

(defun mpsubn-wmpn-precondition-p
    (size-word nr nx ny)
  (let ((size
         (mpsubn-signed32 size-word)))
    (and
     (<= 0 size)
     (mpsubn-valid-p nr size)
     (mpsubn-valid-p nx size)
     (mpsubn-valid-p ny size)
     (mpsubn-result-alias-safe-p
      nr nx size)
     (mpsubn-result-alias-safe-p
      nr ny size)
     (equal
      (mpsubn-data nr)
      (mpsubn-data nx))
     (equal
      (mpsubn-data nx)
      (mpsubn-data ny))
     (equal
      (mpsubn-writable nr)
      t))))

(defun mpsubn-open-state-body-p
    (size-word r x y r1 x1 y1 nr nx ny m)
  (implies
   (mpsubn-open-state-hyp-p
    size-word r x y r1 x1 y1 nr nx ny m)
   (and
    (mpsubn-wmpn-precondition-p
     size-word nr nx ny)
    (mpsubn-all-copied-states-p
     size-word r x y r1 x1 y1 nr nx ny m))))

(defun-sk mpsubn-all-open-states-p
    (size-word r x y r1 x1 y1)
  (forall (nr nx ny m)
    (implies
     (and
      (mpsubn-pointer-p nr)
      (mpsubn-pointer-p nx)
      (mpsubn-pointer-p ny)
      (mpsubn-memory-p m))
     (mpsubn-open-state-body-p
      size-word r x y r1 x1 y1 nr nx ny m))))

(defun mpsubn-initial-copy-body-p
    (size-word r x y y1 x1 r1)
  (implies
   (mpsubn-view-p y1 y)
   (implies
    (mpsubn-view-p x1 x)
    (implies
     (mpsubn-view-p r1 r)
     (mpsubn-all-open-states-p
      size-word r x y r1 x1 y1)))))

(defun-sk mpsubn-all-initial-copies-p
    (size-word r x y)
  (forall (y1 x1 r1)
    (implies
     (and
      (mpsubn-pointer-p y1)
      (mpsubn-pointer-p x1)
      (mpsubn-pointer-p r1))
     (mpsubn-initial-copy-body-p
      size-word r x y y1 x1 r1))))

(defun-sk
    ntp4vc-pearl-multiprecision-sub-sub-sub-nqtvc-statement
    ()
  (forall (size-word r x y)
    (implies
     (and
      (mpsubn-interface-p)
      (mpsubn-bv32-p size-word)
      (mpsubn-pointer-p r)
      (mpsubn-pointer-p x)
      (mpsubn-pointer-p y)
      (<= 0
          (mpsubn-signed32 size-word))
      (mpsubn-valid-p
       r
       (mpsubn-signed32 size-word))
      (mpsubn-valid-p
       x
       (mpsubn-signed32 size-word))
      (mpsubn-valid-p
       y
       (mpsubn-signed32 size-word))
      (equal
       (mpsubn-writable r)
       t))
     (and
      (mpsubn-valid-p
       r
       (mpsubn-signed32 size-word))
      (mpsubn-valid-p
       x
       (mpsubn-signed32 size-word))
      (mpsubn-valid-p
       y
       (mpsubn-signed32 size-word))
      (equal
       (mpsubn-writable r)
       t)
      (<= 0
          (mpsubn-signed32 size-word))
      (<= (mpsubn-signed32 size-word)
          (mpsubn-signed32 size-word))
      (mpsubn-all-initial-copies-p
       size-word r x y)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
