;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_Sub_sub_n_ryqtvc: the verification condition for
;; alias-aware in-place multiprecision subtraction into the second operand,
;; including borrow, memory-frame, validity, and value preservation
;; obligations. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Fixed-width words are represented by their canonical unsigned integers.

(defun subry-bv32-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 4294967296)))

(defun subry-bv64-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 18446744073709551616)))

(defun subry-sint32 (word)
  (if (< word 2147483648)
      word
    (- word 4294967296)))

;; Arrays remain arbitrary total integer-indexed maps.  The raw operation
;; symbols are arbitrary; their normalized observations give every ACL2
;; object a natural length and a 64-bit limb at every integer index.  Thus the
;; array carrier is nonempty and fully typed without restricting its elements
;; to a finite table or otherwise narrowing the source domain.

(defstub subry-array-raw-length (array) t)
(defstub subry-array-raw-elt (array index) t)

(defun subry-array-length (array)
  (nfix (subry-array-raw-length array)))

(defun subry-array-elt (array index)
  (mod
   (ifix (subry-array-raw-elt array index))
   18446744073709551616))

(defun subry-limb-array-p (array)
  (declare (ignore array))
  t)

;; Source-array equality is extensional: equal natural lengths and equal
;; 64-bit limbs at every integer index.  This is the source record equality
;; for a length paired with a total integer-indexed element map.

(defun-sk subry-array-elements-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (subry-array-elt left index)
      (subry-array-elt right index)))))

(defun subry-array-equal-p (left right)
  (and
   (equal
    (subry-array-length left)
    (subry-array-length right))
   (subry-array-elements-equal-p left right)))

;; A pointer is the source record
;;   (data, offset, min, max, writable, zone).
;; The zone carrier is intentionally arbitrary.

(defun subry-ptr-p (pointer)
  (and
   (true-listp pointer)
   (equal (len pointer) 7)
   (equal (nth 0 pointer) :subry-ptr)
   (subry-limb-array-p (nth 1 pointer))
   (integerp (nth 2 pointer))
   (integerp (nth 3 pointer))
   (integerp (nth 4 pointer))
   (booleanp (nth 5 pointer))))

(defun subry-data (pointer)
  (nth 1 pointer))

(defun subry-offset (pointer)
  (nth 2 pointer))

(defun subry-min (pointer)
  (nth 3 pointer))

(defun subry-max (pointer)
  (nth 4 pointer))

(defun subry-writable (pointer)
  (nth 5 pointer))

(defun subry-zone (pointer)
  (nth 6 pointer))

(defun subry-plength (pointer)
  (subry-array-length (subry-data pointer)))

(defun subry-pelts (pointer index)
  (subry-array-elt (subry-data pointer) index))

(defun subry-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

(defun subry-valid-p (pointer size)
  (and
   (subry-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (subry-min pointer))
   (<= (subry-min pointer)
       (subry-offset pointer))
   (<= (+ (subry-offset pointer) size)
       (subry-max pointer))
   (<= (subry-max pointer)
       (subry-plength pointer))))

;; Little-endian base-2^64 value of SIZE limbs beginning at the pointer
;; offset.  All occurrences in the VC have nonnegative SIZE.

(defun subry-value-aux (array index count)
  (if (zp count)
      0
    (+ (subry-array-elt array index)
       (* 18446744073709551616
          (subry-value-aux
           array (+ index 1) (1- count))))))

(defun subry-value (pointer size)
  (subry-value-aux
   (subry-data pointer)
   (subry-offset pointer)
   (nfix size)))

(defun-sk subry-map-eq-sub-p
    (left right lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (subry-pelts left index)
       (subry-pelts right index))))))

(defun-sk subry-map-eq-sub-shift-p
    (left right left-offset right-offset size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index size))
      (equal
       (subry-pelts left (+ left-offset index))
       (subry-pelts right (+ right-offset index)))))))

(defun-sk subry-outside-equal-p
    (current old start size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index start)
       (<= (+ start size) index))
      (equal
       (subry-pelts current index)
       (subry-pelts old index))))))

(defun-sk subry-everywhere-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (subry-pelts left index)
      (subry-pelts right index)))))

;; Alias metadata is the source record
;;   (zr, zx, zy, mr, mx, my, lr, lx, ly, ok).

(defun subry-mem-p (memory)
  (and
   (true-listp memory)
   (equal (len memory) 11)
   (equal (nth 0 memory) :subry-mem)
   (subry-bv32-p (nth 4 memory))
   (subry-bv32-p (nth 5 memory))
   (subry-bv32-p (nth 6 memory))
   (subry-bv32-p (nth 7 memory))
   (subry-bv32-p (nth 8 memory))
   (subry-bv32-p (nth 9 memory))
   (booleanp (nth 10 memory))))

(defun subry-zr (memory)
  (nth 1 memory))

(defun subry-zx (memory)
  (nth 2 memory))

(defun subry-zy (memory)
  (nth 3 memory))

(defun subry-mr (memory)
  (nth 4 memory))

(defun subry-mx (memory)
  (nth 5 memory))

(defun subry-my (memory)
  (nth 6 memory))

(defun subry-lr (memory)
  (nth 7 memory))

(defun subry-lx (memory)
  (nth 8 memory))

(defun subry-ly (memory)
  (nth 9 memory))

(defun subry-ok (memory)
  (nth 10 memory))

(defun subry-identical-p (left right)
  (and
   (subry-array-equal-p
    (subry-data left)
    (subry-data right))
   (equal (subry-offset left)
          (subry-offset right))
   (equal (subry-min left)
          (subry-min right))
   (equal (subry-max left)
          (subry-max right))
   (equal (subry-zone left)
          (subry-zone right))))

(defun subry-view-p (current old)
  (and
   (equal (subry-offset current)
          (subry-offset old))
   (equal (subry-writable current)
          (subry-writable old))
   (equal (subry-zone current)
          (subry-zone old))))

(defun subry-view-with-min-p (current old)
  (and
   (equal (subry-offset current)
          (subry-offset old))
   (equal (subry-min current)
          (subry-min old))
   (equal (subry-writable current)
          (subry-writable old))
   (equal (subry-zone current)
          (subry-zone old))))

(defun subry-full-view-p (current old)
  (and
   (equal (subry-offset current)
          (subry-offset old))
   (equal (subry-min current)
          (subry-min old))
   (equal (subry-max current)
          (subry-max old))
   (equal (subry-writable current)
          (subry-writable old))
   (equal (subry-zone current)
          (subry-zone old))))

(defun subry-mem-view-p (current old)
  (and
   (equal (subry-zr current) (subry-zr old))
   (equal (subry-zx current) (subry-zx old))
   (equal (subry-zy current) (subry-zy old))
   (equal (subry-mr current) (subry-mr old))
   (equal (subry-mx current) (subry-mx old))
   (equal (subry-my current) (subry-my old))
   (equal (subry-lr current) (subry-lr old))
   (equal (subry-lx current) (subry-lx old))
   (equal (subry-ly current) (subry-ly old))))

(defun subry-disjoint-or-equal-p
    (left right size)
  (or
   (equal (subry-offset left)
          (subry-offset right))
   (<= (+ (subry-offset left) size)
       (subry-offset right))
   (<= (+ (subry-offset right) size)
       (subry-offset left))))

(defun subry-separated-p (left right size)
  (or
   (and
    (<= 0 (subry-offset left))
    (<= (+ (subry-offset left) size)
        (subry-offset right)))
   (and
    (<= 0 (subry-offset right))
    (<= (+ (subry-offset right) size)
        (subry-offset left)))))

(defun subry-rebound-view-p
    (current shared-data-pointer old)
  (and
   (subry-array-equal-p
    (subry-data current)
    (subry-data shared-data-pointer))
   (equal
    (subry-plength shared-data-pointer)
    (subry-plength old))
   (subry-full-view-p current old)))

(defun subry-rebound-result-view-p
    (current shared-data-pointer old)
  (and
   (equal
    (subry-plength shared-data-pointer)
    (subry-plength old))
   (subry-full-view-p current old)))

(defun subry-final-postcondition-p
    (size-word x y y2 x2 result)
  (let ((size (subry-sint32 size-word)))
    (and
     (equal
      (- (subry-value y2 size)
         (* (expt 18446744073709551616
                  (nfix size))
            result))
      (- (subry-value x size)
         (subry-value y size)))
     (<= 0 result)
     (<= result 1)
     (subry-outside-equal-p
      y2 y (subry-offset y2) size)
     (subry-everywhere-equal-p x2 x)
     (equal
      (subry-value x2 size)
      (subry-value x size))
     (equal (subry-min x2) (subry-min x))
     (equal (subry-max x2) (subry-max x))
     (equal
      (subry-plength x2)
      (subry-plength x))
     (equal (subry-min y2) (subry-min y))
     (equal (subry-max y2) (subry-max y))
     (equal
      (subry-plength y2)
      (subry-plength y)))))

;; Preserve the innermost universal continuation generated by close_rx.

(defun-sk subry-close-continuation-p
    (size-word x y y1 x1 nx1 ny1 result memory)
  (forall (memory1 nx2 ny2 y2 x2)
    (implies
     (and
      (subry-mem-p memory1)
      (subry-ptr-p nx2)
      (subry-ptr-p ny2)
      (subry-ptr-p y2)
      (subry-ptr-p x2))
     (implies
      (subry-mem-view-p memory1 memory)
      (implies
       (subry-view-p nx2 nx1)
       (implies
        (subry-view-p ny2 ny1)
        (implies
         (subry-view-with-min-p y2 y1)
         (implies
          (subry-view-with-min-p x2 x1)
          (let ((size (subry-sint32 size-word)))
            (implies
             (and
              (equal
               (subry-max y2)
               (subry-sint32
                (subry-mx memory1)))
              (equal
               (subry-max x2)
               (subry-sint32
                (subry-my memory1)))
              (subry-map-eq-sub-shift-p
               ny1 y2
               (subry-offset ny2)
               (subry-offset y2)
               size)
              (subry-map-eq-sub-shift-p
               nx1 x2
               (subry-offset nx2)
               (subry-offset x2)
               size)
              (subry-outside-equal-p
               y2 y1 (subry-offset y2) size)
              (subry-outside-equal-p
               x2 x1 (subry-offset x2) size)
              (equal
               (subry-plength y2)
               (subry-plength y1))
              (equal
               (subry-plength x2)
               (subry-plength x1))
              (equal (subry-min y2)
                     (subry-min y1))
              (equal (subry-min x2)
                     (subry-min x1)))
             (subry-final-postcondition-p
              size-word x y y2 x2 result)))))))))))

(defun subry-result-hypothesis-p
    (size-word nr1 nr nx1 nx ny1 ny result)
  (let ((size (subry-sint32 size-word)))
    (and
     (equal
      (- (subry-value nr1 size)
         (* (expt 18446744073709551616
                  (nfix size))
            result))
      (- (subry-value nx size)
         (subry-value ny size)))
     (<= 0 result)
     (<= result 1)
     (subry-outside-equal-p
      nr1 nr (subry-offset nr1) size)
     (or
      (equal
       (subry-offset nr1)
       (subry-offset nx1))
      (subry-map-eq-sub-p
       nx1 nx
       (subry-offset nx1)
       (+ (subry-offset nx1) size)))
     (or
      (equal
       (subry-offset nr1)
       (subry-offset ny1))
      (subry-map-eq-sub-p
       ny1 ny
       (subry-offset ny1)
       (+ (subry-offset ny1) size))))))

(defun subry-preclose-p
    (size-word y1 x1 nr1 ny1 nx1 memory)
  (let ((size (subry-sint32 size-word)))
    (and
     (equal (subry-writable y1) t)
     (equal (subry-writable nr1) t)
     (equal (subry-ok memory) t)
     (<= 0 size)
     (<= size size)
     (subry-identical-p nr1 ny1)
     (subry-separated-p ny1 nx1 size)
     (equal (subry-zx memory)
            (subry-zone y1))
     (equal (subry-zy memory)
            (subry-zone x1))
     (equal (subry-lx memory)
            size-word)
     (equal (subry-ly memory)
            size-word))))

(defun-sk subry-result-continuation-p
    (size-word x y y1 x1 nr ny nx memory nx1 ny1 nr1)
  (forall (result)
    (implies
     (subry-bv64-p result)
     (implies
      (subry-result-hypothesis-p
       size-word nr1 nr nx1 nx ny1 ny result)
      (and
       (subry-preclose-p
        size-word y1 x1 nr1 ny1 nx1 memory)
       (subry-close-continuation-p
        size-word x y y1 x1 nx1 ny1
        result memory))))))

(defun-sk subry-rebound-continuation-p
    (size-word x y y1 x1 nr ny nx memory)
  (forall (nx1 ny1 nr1)
    (implies
     (and
      (subry-ptr-p nx1)
      (subry-ptr-p ny1)
      (subry-ptr-p nr1))
     (implies
      (subry-rebound-view-p nx1 nr1 nx)
      (implies
       (subry-rebound-view-p ny1 nr1 ny)
       (implies
        (subry-rebound-result-view-p nr1 nr1 nr)
        (subry-result-continuation-p
         size-word x y y1 x1
         nr ny nx memory nx1 ny1 nr1)))))))

(defun subry-open-hypothesis-p
    (size-word x y y1 x1 nr ny nx memory)
  (let ((size (subry-sint32 size-word)))
    (and
     (equal (subry-writable nr) t)
     (equal
      (subry-value ny size)
      (subry-value y size))
     (equal
      (subry-value nx size)
      (subry-value x size))
     (subry-valid-p ny size)
     (subry-valid-p nx size)
     (subry-identical-p nr ny)
     (subry-separated-p ny nx size)
     (equal (subry-zx memory)
            (subry-zone y1))
     (equal (subry-zy memory)
            (subry-zone x1))
     (equal
      (subry-sint32 (subry-mx memory))
      (subry-max y))
     (equal
      (subry-sint32 (subry-my memory))
      (subry-max x))
     (equal (subry-lx memory) size-word)
     (equal (subry-ly memory) size-word)
     (equal (subry-ok memory) t)
     (subry-map-eq-sub-shift-p
      ny y1
      (subry-offset ny)
      (subry-offset y1)
      size)
     (subry-map-eq-sub-shift-p
      nx x1
      (subry-offset nx)
      (subry-offset x1)
      size)
     (subry-everywhere-equal-p y1 y)
     (subry-everywhere-equal-p x1 x)
     (equal
      (subry-plength y1)
      (subry-plength y))
     (equal
      (subry-plength x1)
      (subry-plength x))
     (equal (subry-min y1)
            (subry-min y))
     (equal (subry-min x1)
            (subry-min x))
     (subry-array-equal-p
      (subry-data nr)
      (subry-data ny))
     (subry-array-equal-p
      (subry-data ny)
      (subry-data nx)))))

(defun subry-open-conclusion-p
    (size-word nr ny nx)
  (let ((size (subry-sint32 size-word)))
    (and
     (<= 0 size)
     (subry-valid-p nr size)
     (subry-valid-p nx size)
     (subry-valid-p ny size)
     (subry-disjoint-or-equal-p nr nx size)
     (subry-disjoint-or-equal-p nr ny size)
     (subry-array-equal-p
      (subry-data nr)
      (subry-data nx))
     (subry-array-equal-p
      (subry-data nx)
      (subry-data ny))
     (equal (subry-writable nr) t))))

(defun-sk subry-open-continuation-p
    (size-word x y y1 x1)
  (forall (nr ny nx memory)
    (implies
     (and
      (subry-ptr-p nr)
      (subry-ptr-p ny)
      (subry-ptr-p nx)
      (subry-mem-p memory))
     (implies
      (subry-open-hypothesis-p
       size-word x y y1 x1 nr ny nx memory)
      (and
       (subry-open-conclusion-p
        size-word nr ny nx)
       (subry-rebound-continuation-p
        size-word x y y1 x1
        nr ny nx memory))))))

(defun-sk subry-view-continuation-p
    (size-word x y)
  (forall (y1 x1)
    (implies
     (and
      (subry-ptr-p y1)
      (subry-ptr-p x1))
     (implies
      (subry-view-p y1 y)
      (implies
       (subry-view-p x1 x)
       (subry-open-continuation-p
        size-word x y y1 x1))))))

(defun
    ntp4vc-pearl-multiprecision-sub-sub-sub-n-ryqtvc-statement
    (size-word x y)
  (let ((size (subry-sint32 size-word)))
    (implies
     (and
      (subry-bv32-p size-word)
      (subry-ptr-p x)
      (subry-ptr-p y)
      (<= 0 size)
      (subry-valid-p x size)
      (subry-valid-p y size)
      (equal (subry-writable y) t))
     (and
      (subry-valid-p y size)
      (subry-valid-p x size)
      (<= 0 size)
      (<= size size)
      (equal (subry-writable y) t)
      (subry-view-continuation-p
       size-word x y)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
