;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_Sub_sub_rxqtvc: the verification condition for
;; alias-aware unequal-length multiprecision subtraction into the first
;; operand, including borrow, memory framing, validity, and preservation of
;; the second operand and pointer metadata. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Fixed-width words are represented by their canonical unsigned integers.

(defun subrx-bv32-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 4294967296)))

(defun subrx-bv64-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 18446744073709551616)))

(defun subrx-sint32 (word)
  (if (< word 2147483648)
      word
    (- word 4294967296)))

;; Arrays remain arbitrary total integer-indexed maps.  The raw operation
;; symbols are arbitrary; their normalized observations give every ACL2
;; object a natural length and a 64-bit limb at every integer index.  Thus the
;; array carrier is nonempty and fully typed without restricting its elements
;; to a finite table or otherwise narrowing the source domain.

(defstub subrx-array-raw-length (array) t)
(defstub subrx-array-raw-elt (array index) t)

(defun subrx-array-length (array)
  (nfix (subrx-array-raw-length array)))

(defun subrx-array-elt (array index)
  (mod
   (ifix (subrx-array-raw-elt array index))
   18446744073709551616))

(defun subrx-limb-array-p (array)
  (declare (ignore array))
  t)

;; Source-array equality is extensional: equal natural lengths and equal
;; 64-bit limbs at every integer index.  This is the source record equality
;; for a length paired with a total integer-indexed element map.

(defun-sk subrx-array-elements-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (subrx-array-elt left index)
      (subrx-array-elt right index)))))

(defun subrx-array-equal-p (left right)
  (and
   (equal
    (subrx-array-length left)
    (subrx-array-length right))
   (subrx-array-elements-equal-p left right)))

;; A pointer is the source record
;;   (data, offset, min, max, writable, zone).
;; The zone carrier is intentionally arbitrary.

(defun subrx-ptr-p (pointer)
  (and
   (true-listp pointer)
   (equal (len pointer) 7)
   (equal (nth 0 pointer) :subrx-ptr)
   (subrx-limb-array-p (nth 1 pointer))
   (integerp (nth 2 pointer))
   (integerp (nth 3 pointer))
   (integerp (nth 4 pointer))
   (booleanp (nth 5 pointer))))

(defun subrx-data (pointer)
  (nth 1 pointer))

(defun subrx-offset (pointer)
  (nth 2 pointer))

(defun subrx-min (pointer)
  (nth 3 pointer))

(defun subrx-max (pointer)
  (nth 4 pointer))

(defun subrx-writable (pointer)
  (nth 5 pointer))

(defun subrx-zone (pointer)
  (nth 6 pointer))

(defun subrx-plength (pointer)
  (subrx-array-length (subrx-data pointer)))

(defun subrx-pelts (pointer index)
  (subrx-array-elt (subrx-data pointer) index))

(defun subrx-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

(defun subrx-valid-p (pointer size)
  (and
   (subrx-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (subrx-min pointer))
   (<= (subrx-min pointer)
       (subrx-offset pointer))
   (<= (+ (subrx-offset pointer) size)
       (subrx-max pointer))
   (<= (subrx-max pointer)
       (subrx-plength pointer))))

;; Little-endian base-2^64 value of SIZE limbs beginning at the pointer
;; offset.  All occurrences in the VC have nonnegative SIZE.

(defun subrx-value-aux (array index count)
  (if (zp count)
      0
    (+ (subrx-array-elt array index)
       (* 18446744073709551616
          (subrx-value-aux
           array (+ index 1) (1- count))))))

(defun subrx-value (pointer size)
  (subrx-value-aux
   (subrx-data pointer)
   (subrx-offset pointer)
   (nfix size)))

(defun-sk subrx-map-eq-sub-p
    (left right lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (subrx-pelts left index)
       (subrx-pelts right index))))))

(defun-sk subrx-map-eq-sub-shift-p
    (left right left-offset right-offset size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index size))
      (equal
       (subrx-pelts left (+ left-offset index))
       (subrx-pelts right (+ right-offset index)))))))

(defun-sk subrx-outside-equal-p
    (current old start size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index start)
       (<= (+ start size) index))
      (equal
       (subrx-pelts current index)
       (subrx-pelts old index))))))

(defun-sk subrx-everywhere-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (subrx-pelts left index)
      (subrx-pelts right index)))))

;; Alias metadata is the source record
;;   (zr, zx, zy, mr, mx, my, lr, lx, ly, ok).

(defun subrx-mem-p (memory)
  (and
   (true-listp memory)
   (equal (len memory) 11)
   (equal (nth 0 memory) :subrx-mem)
   (subrx-bv32-p (nth 4 memory))
   (subrx-bv32-p (nth 5 memory))
   (subrx-bv32-p (nth 6 memory))
   (subrx-bv32-p (nth 7 memory))
   (subrx-bv32-p (nth 8 memory))
   (subrx-bv32-p (nth 9 memory))
   (booleanp (nth 10 memory))))

(defun subrx-zr (memory)
  (nth 1 memory))

(defun subrx-zx (memory)
  (nth 2 memory))

(defun subrx-zy (memory)
  (nth 3 memory))

(defun subrx-mr (memory)
  (nth 4 memory))

(defun subrx-mx (memory)
  (nth 5 memory))

(defun subrx-my (memory)
  (nth 6 memory))

(defun subrx-lr (memory)
  (nth 7 memory))

(defun subrx-lx (memory)
  (nth 8 memory))

(defun subrx-ly (memory)
  (nth 9 memory))

(defun subrx-ok (memory)
  (nth 10 memory))

(defun subrx-identical-p (left right)
  (and
   (subrx-array-equal-p
    (subrx-data left)
    (subrx-data right))
   (equal (subrx-offset left)
          (subrx-offset right))
   (equal (subrx-min left)
          (subrx-min right))
   (equal (subrx-max left)
          (subrx-max right))
   (equal (subrx-zone left)
          (subrx-zone right))))

(defun subrx-view-p (current old)
  (and
   (equal (subrx-offset current)
          (subrx-offset old))
   (equal (subrx-writable current)
          (subrx-writable old))
   (equal (subrx-zone current)
          (subrx-zone old))))

(defun subrx-view-with-min-p (current old)
  (and
   (equal (subrx-offset current)
          (subrx-offset old))
   (equal (subrx-min current)
          (subrx-min old))
   (equal (subrx-writable current)
          (subrx-writable old))
   (equal (subrx-zone current)
          (subrx-zone old))))

(defun subrx-full-view-p (current old)
  (and
   (equal (subrx-offset current)
          (subrx-offset old))
   (equal (subrx-min current)
          (subrx-min old))
   (equal (subrx-max current)
          (subrx-max old))
   (equal (subrx-writable current)
          (subrx-writable old))
   (equal (subrx-zone current)
          (subrx-zone old))))

(defun subrx-mem-view-p (current old)
  (and
   (equal (subrx-zr current) (subrx-zr old))
   (equal (subrx-zx current) (subrx-zx old))
   (equal (subrx-zy current) (subrx-zy old))
   (equal (subrx-mr current) (subrx-mr old))
   (equal (subrx-mx current) (subrx-mx old))
   (equal (subrx-my current) (subrx-my old))
   (equal (subrx-lr current) (subrx-lr old))
   (equal (subrx-lx current) (subrx-lx old))
   (equal (subrx-ly current) (subrx-ly old))))

(defun subrx-disjoint-or-equal-p
    (result operand result-size operand-size)
  (or
   (equal (subrx-offset result)
          (subrx-offset operand))
   (<= (+ (subrx-offset result) result-size)
       (subrx-offset operand))
   (<= (+ (subrx-offset operand) operand-size)
       (subrx-offset result))))

(defun subrx-separated-p
    (left right left-size right-size)
  (or
   (and
    (<= 0 (subrx-offset left))
    (<= (+ (subrx-offset left) left-size)
        (subrx-offset right)))
   (and
    (<= 0 (subrx-offset right))
    (<= (+ (subrx-offset right) right-size)
        (subrx-offset left)))))

(defun subrx-rebound-view-p
    (current shared-data-pointer old)
  (and
   (subrx-array-equal-p
    (subrx-data current)
    (subrx-data shared-data-pointer))
   (equal
    (subrx-plength shared-data-pointer)
    (subrx-plength old))
   (subrx-full-view-p current old)))

(defun subrx-rebound-result-view-p
    (current shared-data-pointer old)
  (and
   (equal
    (subrx-plength shared-data-pointer)
    (subrx-plength old))
   (subrx-full-view-p current old)))

(defun subrx-final-postcondition-p
    (sx-word sy-word x y x2 y2 result)
  (let ((sx (subrx-sint32 sx-word))
        (sy (subrx-sint32 sy-word)))
    (and
     (equal
      (- (subrx-value x2 sx)
         (* (expt 18446744073709551616
                  (nfix sx))
            result))
      (- (subrx-value x sx)
         (subrx-value y sy)))
     (<= 0 result)
     (<= result 1)
     (subrx-outside-equal-p
      x2 x (subrx-offset x2) sx)
     (subrx-everywhere-equal-p y2 y)
     (equal
      (subrx-value y2 sy)
      (subrx-value y sy))
     (equal (subrx-min x2) (subrx-min x))
     (equal (subrx-max x2) (subrx-max x))
     (equal
      (subrx-plength x2)
      (subrx-plength x))
     (equal (subrx-min y2) (subrx-min y))
     (equal (subrx-max y2) (subrx-max y))
     (equal
      (subrx-plength y2)
      (subrx-plength y)))))

;; Preserve the innermost universal continuation generated by close_rx.

(defun-sk subrx-close-continuation-p
    (sx-word sy-word x y x1 y1 result memory nx1 ny1)
  (forall (memory1 ny2 nx2 y2 x2)
    (implies
     (and
      (subrx-mem-p memory1)
      (subrx-ptr-p ny2)
      (subrx-ptr-p nx2)
      (subrx-ptr-p y2)
      (subrx-ptr-p x2))
     (implies
      (subrx-mem-view-p memory1 memory)
      (implies
       (subrx-view-p ny2 ny1)
       (implies
        (subrx-view-p nx2 nx1)
        (implies
         (subrx-view-with-min-p y2 y1)
         (implies
          (subrx-view-with-min-p x2 x1)
          (let ((sx (subrx-sint32 sx-word))
                (sy (subrx-sint32 sy-word)))
            (implies
             (and
              (equal
               (subrx-max x2)
               (subrx-sint32
                (subrx-mx memory1)))
              (equal
               (subrx-max y2)
               (subrx-sint32
                (subrx-my memory1)))
              (subrx-map-eq-sub-shift-p
               nx1 x2
               (subrx-offset nx2)
               (subrx-offset x2)
               sx)
              (subrx-map-eq-sub-shift-p
               ny1 y2
               (subrx-offset ny2)
               (subrx-offset y2)
               sy)
              (subrx-outside-equal-p
               x2 x1 (subrx-offset x2) sx)
              (subrx-outside-equal-p
               y2 y1 (subrx-offset y2) sy)
              (equal
               (subrx-plength x2)
               (subrx-plength x1))
              (equal
               (subrx-plength y2)
               (subrx-plength y1))
              (equal (subrx-min x2)
                     (subrx-min x1))
              (equal (subrx-min y2)
                     (subrx-min y1)))
             (subrx-final-postcondition-p
              sx-word sy-word x y x2 y2 result)))))))))))

(defun subrx-result-hypothesis-p
    (sx-word sy-word nr1 nr nx1 nx ny1 ny result)
  (let ((sx (subrx-sint32 sx-word))
        (sy (subrx-sint32 sy-word)))
    (and
     (equal
      (- (subrx-value nr1 sx)
         (* (expt 18446744073709551616
                  (nfix sx))
            result))
      (- (subrx-value nx sx)
         (subrx-value ny sy)))
     (<= 0 result)
     (<= result 1)
     (subrx-outside-equal-p
      nr1 nr (subrx-offset nr1) sx)
     (or
      (equal
       (subrx-offset nr1)
       (subrx-offset nx1))
      (subrx-map-eq-sub-p
       nx1 nx
       (subrx-offset nx1)
       (+ (subrx-offset nx1) sx)))
     (or
      (equal
       (subrx-offset nr1)
       (subrx-offset ny1))
      (subrx-map-eq-sub-p
       ny1 ny
       (subrx-offset ny1)
       (+ (subrx-offset ny1) sy))))))

(defun subrx-preclose-p
    (sx-word sy-word x1 y1 nr1 nx1 ny1 memory)
  (let ((sx (subrx-sint32 sx-word))
        (sy (subrx-sint32 sy-word)))
    (and
     (equal (subrx-writable x1) t)
     (equal (subrx-writable nr1) t)
     (equal (subrx-ok memory) t)
     (<= 0 sy)
     (<= sy sx)
     (subrx-identical-p nr1 nx1)
     (subrx-separated-p nx1 ny1 sx sy)
     (equal (subrx-zx memory)
            (subrx-zone x1))
     (equal (subrx-zy memory)
            (subrx-zone y1))
     (equal (subrx-lx memory)
            sx-word)
     (equal (subrx-ly memory)
            sy-word))))

(defun-sk subrx-result-continuation-p
    (sx-word sy-word x y x1 y1 nr nx ny memory nx1 ny1 nr1)
  (forall (result)
    (implies
     (subrx-bv64-p result)
     (implies
      (subrx-result-hypothesis-p
       sx-word sy-word nr1 nr nx1 nx ny1 ny result)
      (and
       (subrx-preclose-p
        sx-word sy-word x1 y1 nr1 nx1 ny1 memory)
       (subrx-close-continuation-p
        sx-word sy-word x y x1 y1 result memory nx1 ny1))))))

(defun-sk subrx-rebound-continuation-p
    (sx-word sy-word x y x1 y1 nr nx ny memory)
  (forall (ny1 nx1 nr1)
    (implies
     (and
      (subrx-ptr-p ny1)
      (subrx-ptr-p nx1)
      (subrx-ptr-p nr1))
     (implies
      (subrx-rebound-view-p ny1 nr1 ny)
      (implies
       (subrx-rebound-view-p nx1 nr1 nx)
       (implies
        (subrx-rebound-result-view-p nr1 nr1 nr)
        (subrx-result-continuation-p
         sx-word sy-word x y x1 y1
         nr nx ny memory nx1 ny1 nr1)))))))

(defun subrx-open-hypothesis-p
    (sx-word sy-word x y x1 y1 nr nx ny memory)
  (let ((sx (subrx-sint32 sx-word))
        (sy (subrx-sint32 sy-word)))
    (and
     (equal (subrx-writable nr) t)
     (equal
      (subrx-value nx sx)
      (subrx-value x sx))
     (equal
      (subrx-value ny sy)
      (subrx-value y sy))
     (subrx-valid-p nx sx)
     (subrx-valid-p ny sy)
     (subrx-identical-p nr nx)
     (subrx-separated-p nx ny sx sy)
     (equal (subrx-zx memory)
            (subrx-zone x1))
     (equal (subrx-zy memory)
            (subrx-zone y1))
     (equal
      (subrx-sint32 (subrx-mx memory))
      (subrx-max x))
     (equal
      (subrx-sint32 (subrx-my memory))
      (subrx-max y))
     (equal (subrx-lx memory) sx-word)
     (equal (subrx-ly memory) sy-word)
     (equal (subrx-ok memory) t)
     (subrx-map-eq-sub-shift-p
      nx x1
      (subrx-offset nx)
      (subrx-offset x1)
      sx)
     (subrx-map-eq-sub-shift-p
      ny y1
      (subrx-offset ny)
      (subrx-offset y1)
      sy)
     (subrx-everywhere-equal-p x1 x)
     (subrx-everywhere-equal-p y1 y)
     (equal
      (subrx-plength x1)
      (subrx-plength x))
     (equal
      (subrx-plength y1)
      (subrx-plength y))
     (equal (subrx-min x1)
            (subrx-min x))
     (equal (subrx-min y1)
            (subrx-min y))
     (subrx-array-equal-p
      (subrx-data nr)
      (subrx-data nx))
     (subrx-array-equal-p
      (subrx-data nx)
      (subrx-data ny)))))

(defun subrx-open-conclusion-p
    (sx-word sy-word nr nx ny)
  (let ((sx (subrx-sint32 sx-word))
        (sy (subrx-sint32 sy-word)))
    (and
     (<= 0 sy)
     (<= sy sx)
     (subrx-valid-p nr sx)
     (subrx-valid-p nx sx)
     (subrx-valid-p ny sy)
     (subrx-disjoint-or-equal-p nr nx sx sx)
     (subrx-disjoint-or-equal-p nr ny sx sy)
     (subrx-array-equal-p
      (subrx-data nr)
      (subrx-data nx))
     (subrx-array-equal-p
      (subrx-data nx)
      (subrx-data ny))
     (equal (subrx-writable nr) t))))

(defun-sk subrx-open-continuation-p
    (sx-word sy-word x y x1 y1)
  (forall (nr nx ny memory)
    (implies
     (and
      (subrx-ptr-p nr)
      (subrx-ptr-p nx)
      (subrx-ptr-p ny)
      (subrx-mem-p memory))
     (implies
      (subrx-open-hypothesis-p
       sx-word sy-word x y x1 y1 nr nx ny memory)
      (and
       (subrx-open-conclusion-p
        sx-word sy-word nr nx ny)
       (subrx-rebound-continuation-p
        sx-word sy-word x y x1 y1
        nr nx ny memory))))))

(defun-sk subrx-view-continuation-p
    (sx-word sy-word x y)
  (forall (y1 x1)
    (implies
     (and
      (subrx-ptr-p y1)
      (subrx-ptr-p x1))
     (implies
      (subrx-view-p y1 y)
      (implies
       (subrx-view-p x1 x)
       (subrx-open-continuation-p
        sx-word sy-word x y x1 y1))))))

(defun-sk
    ntp4vc-pearl-multiprecision-sub-sub-sub-rxqtvc-statement
    ()
  (forall (sy-word sx-word x y)
    (implies
     (and
      (subrx-bv32-p sy-word)
      (subrx-bv32-p sx-word)
      (subrx-ptr-p x)
      (subrx-ptr-p y)
      (<= 0 (subrx-sint32 sy-word))
      (<= (subrx-sint32 sy-word)
          (subrx-sint32 sx-word))
      (subrx-valid-p x (subrx-sint32 sx-word))
      (subrx-valid-p y (subrx-sint32 sy-word))
      (equal (subrx-writable x) t))
     (and
      (subrx-valid-p x (subrx-sint32 sx-word))
      (subrx-valid-p y (subrx-sint32 sy-word))
      (<= 0 (subrx-sint32 sy-word))
      (<= (subrx-sint32 sy-word)
          (subrx-sint32 sx-word))
      (equal (subrx-writable x) t)
      (subrx-view-continuation-p
       sx-word sy-word x y)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
