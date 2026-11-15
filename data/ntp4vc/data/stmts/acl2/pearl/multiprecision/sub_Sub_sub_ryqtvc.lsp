;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_Sub_sub_ryqtvc: the multiprecision subtraction
;; verification condition for alias-separated limb arrays, borrow, and
;; preservation of pointer data outside the written range. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^32 and 2^64 are exact representations of the
;; source bit-vector carriers.  SUB-RY-SINT32 is two's-complement signed
;; interpretation, while a represented 64-bit word is already its unsigned
;; interpretation.

(defun sub-ry-word32-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 4294967296)))

(defun sub-ry-sint32 (word)
  (if (< word 2147483648)
      word
    (- word 4294967296)))

(defun sub-ry-word64-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 18446744073709551616)))

;; The source array element maps are total on all mathematical integers.
;; These conservative interfaces therefore retain arbitrary maps rather than
;; replacing them with finite tables.  Pointer and memory predicates encode
;; the source's nonempty typed carriers.

(defstub sub-ry-data-p (data) t)
(defstub sub-ry-data-length (data) t)
(defstub sub-ry-data-elt (data index) t)

(defstub sub-ry-zone-p (zone) t)

(defstub sub-ry-pointer-p (pointer) t)
(defstub sub-ry-pointer-data (pointer) t)
(defstub sub-ry-pointer-offset (pointer) t)
(defstub sub-ry-pointer-min (pointer) t)
(defstub sub-ry-pointer-max (pointer) t)
(defstub sub-ry-pointer-writable (pointer) t)
(defstub sub-ry-pointer-zone (pointer) t)

(defstub sub-ry-memory-p (memory) t)
(defstub sub-ry-memory-zr (memory) t)
(defstub sub-ry-memory-zx (memory) t)
(defstub sub-ry-memory-zy (memory) t)
(defstub sub-ry-memory-mr (memory) t)
(defstub sub-ry-memory-mx (memory) t)
(defstub sub-ry-memory-my (memory) t)
(defstub sub-ry-memory-lr (memory) t)
(defstub sub-ry-memory-lx (memory) t)
(defstub sub-ry-memory-ly (memory) t)
(defstub sub-ry-memory-ok (memory) t)

(defun-sk sub-ry-carriers-inhabited-p ()
  (exists (data zone pointer memory)
    (and
     (sub-ry-data-p data)
     (sub-ry-zone-p zone)
     (sub-ry-pointer-p pointer)
     (sub-ry-memory-p memory))))

(defun-sk sub-ry-data-function-types-p ()
  (forall (data index)
    (implies
     (sub-ry-data-p data)
     (and
      (natp (sub-ry-data-length data))
      (implies
       (integerp index)
       (sub-ry-word64-p
        (sub-ry-data-elt data index)))))))

(defun-sk sub-ry-pointer-function-types-p ()
  (forall (pointer)
    (implies
     (sub-ry-pointer-p pointer)
     (and
      (sub-ry-data-p
       (sub-ry-pointer-data pointer))
      (integerp
       (sub-ry-pointer-offset pointer))
      (integerp
       (sub-ry-pointer-min pointer))
      (integerp
       (sub-ry-pointer-max pointer))
      (booleanp
       (sub-ry-pointer-writable pointer))
      (sub-ry-zone-p
       (sub-ry-pointer-zone pointer))))))

(defun-sk sub-ry-memory-zone-function-types-p ()
  (forall (memory)
    (implies
     (sub-ry-memory-p memory)
     (and
      (sub-ry-zone-p
       (sub-ry-memory-zr memory))
      (sub-ry-zone-p
       (sub-ry-memory-zx memory))
      (sub-ry-zone-p
       (sub-ry-memory-zy memory))))))

(defun-sk sub-ry-memory-word-function-types-p ()
  (forall (memory)
    (implies
     (sub-ry-memory-p memory)
     (and
      (sub-ry-word32-p
       (sub-ry-memory-mr memory))
      (sub-ry-word32-p
       (sub-ry-memory-mx memory))
      (sub-ry-word32-p
       (sub-ry-memory-my memory))
      (sub-ry-word32-p
       (sub-ry-memory-lr memory))
      (sub-ry-word32-p
       (sub-ry-memory-lx memory))
      (sub-ry-word32-p
       (sub-ry-memory-ly memory))))))

(defun-sk sub-ry-memory-ok-function-type-p ()
  (forall (memory)
    (implies
     (sub-ry-memory-p memory)
     (booleanp
      (sub-ry-memory-ok memory)))))

(defun sub-ry-background-p ()
  (and
   (sub-ry-carriers-inhabited-p)
   (sub-ry-data-function-types-p)
   (sub-ry-pointer-function-types-p)
   (sub-ry-memory-zone-function-types-p)
   (sub-ry-memory-word-function-types-p)
   (sub-ry-memory-ok-function-type-p)))

;; Source array equality is equality of the length and of the arbitrary total
;; integer-indexed element map.

(defun-sk sub-ry-data-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (sub-ry-data-elt left index)
      (sub-ry-data-elt right index)))))

(defun sub-ry-array-equal-p (left right)
  (and
   (equal
    (sub-ry-data-length left)
    (sub-ry-data-length right))
   (sub-ry-data-equal-p left right)))

(defun sub-ry-pelts (pointer index)
  (sub-ry-data-elt
   (sub-ry-pointer-data pointer)
   index))

(defun sub-ry-plength (pointer)
  (sub-ry-data-length
   (sub-ry-pointer-data pointer)))

(defun-sk sub-ry-pelts-equal-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (sub-ry-pelts left index)
      (sub-ry-pelts right index)))))

(defun-sk sub-ry-map-eq-sub-p
    (left right lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (sub-ry-pelts left index)
       (sub-ry-pelts right index))))))

(defun-sk sub-ry-map-eq-sub-shift-p
    (left right left-offset right-offset size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index size))
      (equal
       (sub-ry-pelts
        left (+ left-offset index))
       (sub-ry-pelts
        right (+ right-offset index)))))))

(defun-sk sub-ry-outside-equal-p
    (current old lower size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index lower)
       (<= (+ lower size) index))
      (equal
       (sub-ry-pelts current index)
       (sub-ry-pelts old index))))))

;; This is the exact source definition of C.valid for a pointer and signed
;; 32-bit size.

(defun sub-ry-valid-p (pointer size)
  (and
   (integerp size)
   (<= -2147483648 size)
   (<= size 2147483647)
   (<= 0 size)
   (<= 0
       (sub-ry-pointer-min pointer))
   (<= (sub-ry-pointer-min pointer)
       (sub-ry-pointer-offset pointer))
   (<= (+ (sub-ry-pointer-offset pointer)
          size)
       (sub-ry-pointer-max pointer))
   (<= (sub-ry-pointer-max pointer)
       (sub-ry-plength pointer))))

;; Alias.identical is structural equality of data, offset, bounds, and zone;
;; writable status is intentionally not part of this source predicate.

(defun sub-ry-identical-p (left right)
  (and
   (sub-ry-array-equal-p
    (sub-ry-pointer-data left)
    (sub-ry-pointer-data right))
   (equal
    (sub-ry-pointer-offset left)
    (sub-ry-pointer-offset right))
   (equal
    (sub-ry-pointer-min left)
    (sub-ry-pointer-min right))
   (equal
    (sub-ry-pointer-max left)
    (sub-ry-pointer-max right))
   (equal
    (sub-ry-pointer-zone left)
    (sub-ry-pointer-zone right))))

;; Little-endian radix-2^64 value on a finite half-open interval.  For a
;; negative size the source recursive definition also returns zero.

(defun sub-ry-value-count (data index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+
     (sub-ry-data-elt data index)
     (*
      18446744073709551616
      (sub-ry-value-count
       data
       (+ index 1)
       (- count 1))))))

(defun sub-ry-value (pointer size)
  (sub-ry-value-count
   (sub-ry-pointer-data pointer)
   (sub-ry-pointer-offset pointer)
   (nfix size)))

(defun sub-ry-radix-power (size)
  (if (and
       (integerp size)
       (<= 0 size))
      (expt 18446744073709551616 size)
    1))

;; The innermost continuation after close_rx, preserving all quantified
;; memory snapshots and pointer copies.

(defun-sk sub-ry-all-final-states-p
    (sx sy x y y1 x1 nr ny nx memory nx1 ny1 nr1 result)
  (forall (memory1 nx2 ny2 y2 x2)
    (implies
     (and
      (sub-ry-memory-p memory1)
      (sub-ry-pointer-p nx2)
      (sub-ry-pointer-p ny2)
      (sub-ry-pointer-p y2)
      (sub-ry-pointer-p x2))
     (implies
      (and
       (equal
        (sub-ry-memory-zr memory1)
        (sub-ry-memory-zr memory))
       (equal
        (sub-ry-memory-zx memory1)
        (sub-ry-memory-zx memory))
       (equal
        (sub-ry-memory-zy memory1)
        (sub-ry-memory-zy memory))
       (equal
        (sub-ry-memory-mr memory1)
        (sub-ry-memory-mr memory))
       (equal
        (sub-ry-memory-mx memory1)
        (sub-ry-memory-mx memory))
       (equal
        (sub-ry-memory-my memory1)
        (sub-ry-memory-my memory))
       (equal
        (sub-ry-memory-lr memory1)
        (sub-ry-memory-lr memory))
       (equal
        (sub-ry-memory-lx memory1)
        (sub-ry-memory-lx memory))
       (equal
        (sub-ry-memory-ly memory1)
        (sub-ry-memory-ly memory)))
      (implies
       (and
        (equal
         (sub-ry-pointer-offset nx2)
         (sub-ry-pointer-offset nx1))
        (equal
         (sub-ry-pointer-writable nx2)
         (sub-ry-pointer-writable nx1))
        (equal
         (sub-ry-pointer-zone nx2)
         (sub-ry-pointer-zone nx1)))
       (implies
        (and
         (equal
          (sub-ry-pointer-offset ny2)
          (sub-ry-pointer-offset ny1))
         (equal
          (sub-ry-pointer-writable ny2)
          (sub-ry-pointer-writable ny1))
         (equal
          (sub-ry-pointer-zone ny2)
          (sub-ry-pointer-zone ny1)))
        (implies
         (and
          (equal
           (sub-ry-pointer-offset y2)
           (sub-ry-pointer-offset y1))
          (equal
           (sub-ry-pointer-min y2)
           (sub-ry-pointer-min y1))
          (equal
           (sub-ry-pointer-writable y2)
           (sub-ry-pointer-writable y1))
          (equal
           (sub-ry-pointer-zone y2)
           (sub-ry-pointer-zone y1)))
         (implies
          (and
           (equal
            (sub-ry-pointer-offset x2)
            (sub-ry-pointer-offset x1))
           (equal
            (sub-ry-pointer-min x2)
            (sub-ry-pointer-min x1))
           (equal
            (sub-ry-pointer-writable x2)
            (sub-ry-pointer-writable x1))
           (equal
            (sub-ry-pointer-zone x2)
            (sub-ry-pointer-zone x1)))
          (implies
           (and
            (equal
             (sub-ry-pointer-max y2)
             (sub-ry-sint32
              (sub-ry-memory-mx memory1)))
            (equal
             (sub-ry-pointer-max x2)
             (sub-ry-sint32
              (sub-ry-memory-my memory1)))
            (sub-ry-map-eq-sub-shift-p
             ny1 y2
             (sub-ry-pointer-offset ny2)
             (sub-ry-pointer-offset y2)
             (sub-ry-sint32 sx))
            (sub-ry-map-eq-sub-shift-p
             nx1 x2
             (sub-ry-pointer-offset nx2)
             (sub-ry-pointer-offset x2)
             (sub-ry-sint32 sx))
            (sub-ry-outside-equal-p
             y2 y1
             (sub-ry-pointer-offset y2)
             (sub-ry-sint32 sx))
            (sub-ry-outside-equal-p
             x2 x1
             (sub-ry-pointer-offset x2)
             (sub-ry-sint32 sx))
            (equal
             (sub-ry-plength y2)
             (sub-ry-plength y1))
            (equal
             (sub-ry-plength x2)
             (sub-ry-plength x1))
            (equal
             (sub-ry-pointer-min y2)
             (sub-ry-pointer-min y1))
            (equal
             (sub-ry-pointer-min x2)
             (sub-ry-pointer-min x1)))
           (and
            (equal
             (-
              (sub-ry-value
               y2 (sub-ry-sint32 sx))
              (*
               (sub-ry-radix-power
                (sub-ry-sint32 sx))
               result))
             (-
              (sub-ry-value
               x (sub-ry-sint32 sx))
              (sub-ry-value
               y (sub-ry-sint32 sy))))
            (<= 0 result)
            (<= result 1)
            (sub-ry-outside-equal-p
             y2 y
             (sub-ry-pointer-offset y2)
             (sub-ry-sint32 sx))
            (sub-ry-pelts-equal-p x2 x)
            (equal
             (sub-ry-value
              x2 (sub-ry-sint32 sx))
             (sub-ry-value
              x (sub-ry-sint32 sx)))
            (equal
             (sub-ry-pointer-min x2)
             (sub-ry-pointer-min x))
            (equal
             (sub-ry-pointer-max x2)
             (sub-ry-pointer-max x))
            (equal
             (sub-ry-plength x2)
             (sub-ry-plength x))
            (equal
             (sub-ry-pointer-min y2)
             (sub-ry-pointer-min y))
            (equal
             (sub-ry-pointer-max y2)
             (sub-ry-pointer-max y))
            (equal
             (sub-ry-plength y2)
             (sub-ry-plength y))))))))))))

(defun sub-ry-after-result-p
    (sx sy x y y1 x1 nr ny nx memory nx1 ny1 nr1 result)
  (and
   (equal
    (sub-ry-pointer-writable y1)
    t)
   (equal
    (sub-ry-pointer-writable nr1)
    t)
   (equal
    (sub-ry-memory-ok memory)
    t)
   (<= 0 (sub-ry-sint32 sx))
   (<= (sub-ry-sint32 sx)
       (sub-ry-sint32 sx))
   (sub-ry-identical-p nr1 ny1)
   (or
    (and
     (<= 0
         (sub-ry-pointer-offset ny1))
     (<= (+ (sub-ry-pointer-offset ny1)
            (sub-ry-sint32 sx))
         (sub-ry-pointer-offset nx1)))
    (and
     (<= 0
         (sub-ry-pointer-offset nx1))
     (<= (+ (sub-ry-pointer-offset nx1)
            (sub-ry-sint32 sx))
         (sub-ry-pointer-offset ny1))))
   (equal
    (sub-ry-memory-zx memory)
    (sub-ry-pointer-zone y1))
   (equal
    (sub-ry-memory-zy memory)
    (sub-ry-pointer-zone x1))
   (equal
    (sub-ry-memory-lx memory)
    sx)
   (equal
    (sub-ry-memory-ly memory)
    sx)
   (sub-ry-all-final-states-p
    sx sy x y y1 x1 nr ny nx memory
    nx1 ny1 nr1 result)))

(defun-sk sub-ry-all-results-p
    (sx sy x y y1 x1 nr ny nx memory nx1 ny1 nr1)
  (forall (result)
    (implies
     (sub-ry-word64-p result)
     (implies
      (and
       (equal
        (-
         (sub-ry-value
          nr1 (sub-ry-sint32 sx))
         (*
          (sub-ry-radix-power
           (sub-ry-sint32 sx))
          result))
        (-
         (sub-ry-value
          nx (sub-ry-sint32 sx))
         (sub-ry-value
          ny (sub-ry-sint32 sy))))
       (<= 0 result)
       (<= result 1)
       (sub-ry-outside-equal-p
        nr1 nr
        (sub-ry-pointer-offset nr1)
        (sub-ry-sint32 sx))
       (or
        (equal
         (sub-ry-pointer-offset nr1)
         (sub-ry-pointer-offset nx1))
        (sub-ry-map-eq-sub-p
         nx1 nx
         (sub-ry-pointer-offset nx1)
         (+ (sub-ry-pointer-offset nx1)
            (sub-ry-sint32 sx))))
       (or
        (equal
         (sub-ry-pointer-offset nr1)
         (sub-ry-pointer-offset ny1))
        (sub-ry-map-eq-sub-p
         ny1 ny
         (sub-ry-pointer-offset ny1)
         (+ (sub-ry-pointer-offset ny1)
            (sub-ry-sint32 sy)))))
      (sub-ry-after-result-p
       sx sy x y y1 x1 nr ny nx memory
       nx1 ny1 nr1 result)))))

(defun-sk sub-ry-all-relinked-p
    (sx sy x y y1 x1 nr ny nx memory)
  (forall (nx1 ny1 nr1)
    (implies
     (and
      (sub-ry-pointer-p nx1)
      (sub-ry-pointer-p ny1)
      (sub-ry-pointer-p nr1))
     (implies
      (and
       (sub-ry-array-equal-p
        (sub-ry-pointer-data nx1)
        (sub-ry-pointer-data nr1))
       (equal
        (sub-ry-plength nr1)
        (sub-ry-plength nx))
       (equal
        (sub-ry-pointer-offset nx1)
        (sub-ry-pointer-offset nx))
       (equal
        (sub-ry-pointer-min nx1)
        (sub-ry-pointer-min nx))
       (equal
        (sub-ry-pointer-max nx1)
        (sub-ry-pointer-max nx))
       (equal
        (sub-ry-pointer-writable nx1)
        (sub-ry-pointer-writable nx))
       (equal
        (sub-ry-pointer-zone nx1)
        (sub-ry-pointer-zone nx)))
      (implies
       (and
        (sub-ry-array-equal-p
         (sub-ry-pointer-data ny1)
         (sub-ry-pointer-data nr1))
        (equal
         (sub-ry-plength nr1)
         (sub-ry-plength ny))
        (equal
         (sub-ry-pointer-offset ny1)
         (sub-ry-pointer-offset ny))
        (equal
         (sub-ry-pointer-min ny1)
         (sub-ry-pointer-min ny))
        (equal
         (sub-ry-pointer-max ny1)
         (sub-ry-pointer-max ny))
        (equal
         (sub-ry-pointer-writable ny1)
         (sub-ry-pointer-writable ny))
        (equal
         (sub-ry-pointer-zone ny1)
         (sub-ry-pointer-zone ny)))
       (implies
        (and
         (equal
          (sub-ry-plength nr1)
          (sub-ry-plength nr))
         (equal
          (sub-ry-pointer-offset nr1)
          (sub-ry-pointer-offset nr))
         (equal
          (sub-ry-pointer-min nr1)
          (sub-ry-pointer-min nr))
         (equal
          (sub-ry-pointer-max nr1)
          (sub-ry-pointer-max nr))
         (equal
          (sub-ry-pointer-writable nr1)
          (sub-ry-pointer-writable nr))
         (equal
          (sub-ry-pointer-zone nr1)
          (sub-ry-pointer-zone nr)))
        (sub-ry-all-results-p
         sx sy x y y1 x1 nr ny nx memory
         nx1 ny1 nr1)))))))

(defun sub-ry-after-open-p
    (sx sy x y y1 x1 nr ny nx memory)
  (and
   (<= 0 (sub-ry-sint32 sy))
   (<= (sub-ry-sint32 sy)
       (sub-ry-sint32 sx))
   (sub-ry-valid-p
    nr (sub-ry-sint32 sx))
   (sub-ry-valid-p
    nx (sub-ry-sint32 sx))
   (sub-ry-valid-p
    ny (sub-ry-sint32 sy))
   (or
    (equal
     (sub-ry-pointer-offset nr)
     (sub-ry-pointer-offset nx))
    (<= (+ (sub-ry-pointer-offset nr)
           (sub-ry-sint32 sx))
        (sub-ry-pointer-offset nx))
    (<= (+ (sub-ry-pointer-offset nx)
           (sub-ry-sint32 sx))
        (sub-ry-pointer-offset nr)))
   (or
    (equal
     (sub-ry-pointer-offset nr)
     (sub-ry-pointer-offset ny))
    (<= (+ (sub-ry-pointer-offset nr)
           (sub-ry-sint32 sx))
        (sub-ry-pointer-offset ny))
    (<= (+ (sub-ry-pointer-offset ny)
           (sub-ry-sint32 sy))
        (sub-ry-pointer-offset nr)))
   (sub-ry-array-equal-p
    (sub-ry-pointer-data nr)
    (sub-ry-pointer-data nx))
   (sub-ry-array-equal-p
    (sub-ry-pointer-data nx)
    (sub-ry-pointer-data ny))
   (equal
    (sub-ry-pointer-writable nr)
    t)
   (sub-ry-all-relinked-p
    sx sy x y y1 x1 nr ny nx memory)))

(defun-sk sub-ry-all-open-states-p
    (sx sy x y y1 x1)
  (forall (nr ny nx memory)
    (implies
     (and
      (sub-ry-pointer-p nr)
      (sub-ry-pointer-p ny)
      (sub-ry-pointer-p nx)
      (sub-ry-memory-p memory))
     (implies
      (and
       (equal
        (sub-ry-pointer-writable nr)
        t)
       (equal
        (sub-ry-value
         ny (sub-ry-sint32 sx))
        (sub-ry-value
         y (sub-ry-sint32 sx)))
       (equal
        (sub-ry-value
         nx (sub-ry-sint32 sx))
        (sub-ry-value
         x (sub-ry-sint32 sx)))
       (sub-ry-valid-p
        ny (sub-ry-sint32 sx))
       (sub-ry-valid-p
        nx (sub-ry-sint32 sx))
       (sub-ry-identical-p nr ny)
       (or
        (and
         (<= 0
             (sub-ry-pointer-offset ny))
         (<= (+ (sub-ry-pointer-offset ny)
                (sub-ry-sint32 sx))
             (sub-ry-pointer-offset nx)))
        (and
         (<= 0
             (sub-ry-pointer-offset nx))
         (<= (+ (sub-ry-pointer-offset nx)
                (sub-ry-sint32 sx))
             (sub-ry-pointer-offset ny))))
       (equal
        (sub-ry-memory-zx memory)
        (sub-ry-pointer-zone y1))
       (equal
        (sub-ry-memory-zy memory)
        (sub-ry-pointer-zone x1))
       (equal
        (sub-ry-sint32
         (sub-ry-memory-mx memory))
        (sub-ry-pointer-max y))
       (equal
        (sub-ry-sint32
         (sub-ry-memory-my memory))
        (sub-ry-pointer-max x))
       (equal
        (sub-ry-memory-lx memory)
        sx)
       (equal
        (sub-ry-memory-ly memory)
        sx)
       (equal
        (sub-ry-memory-ok memory)
        t)
       (sub-ry-map-eq-sub-shift-p
        ny y1
        (sub-ry-pointer-offset ny)
        (sub-ry-pointer-offset y1)
        (sub-ry-sint32 sx))
       (sub-ry-map-eq-sub-shift-p
        nx x1
        (sub-ry-pointer-offset nx)
        (sub-ry-pointer-offset x1)
        (sub-ry-sint32 sx))
       (sub-ry-pelts-equal-p y1 y)
       (sub-ry-pelts-equal-p x1 x)
       (equal
        (sub-ry-plength y1)
        (sub-ry-plength y))
       (equal
        (sub-ry-plength x1)
        (sub-ry-plength x))
       (equal
        (sub-ry-pointer-min y1)
        (sub-ry-pointer-min y))
       (equal
        (sub-ry-pointer-min x1)
        (sub-ry-pointer-min x))
       (sub-ry-array-equal-p
        (sub-ry-pointer-data nr)
        (sub-ry-pointer-data ny))
       (sub-ry-array-equal-p
        (sub-ry-pointer-data ny)
        (sub-ry-pointer-data nx)))
      (sub-ry-after-open-p
       sx sy x y y1 x1 nr ny nx memory)))))

(defun-sk sub-ry-all-pointer-copies-p
    (sx sy x y)
  (forall (y1 x1)
    (implies
     (and
      (sub-ry-pointer-p y1)
      (sub-ry-pointer-p x1))
     (implies
      (and
       (equal
        (sub-ry-pointer-offset y1)
        (sub-ry-pointer-offset y))
       (equal
        (sub-ry-pointer-writable y1)
        (sub-ry-pointer-writable y))
       (equal
        (sub-ry-pointer-zone y1)
        (sub-ry-pointer-zone y)))
      (implies
       (and
        (equal
         (sub-ry-pointer-offset x1)
         (sub-ry-pointer-offset x))
        (equal
         (sub-ry-pointer-writable x1)
         (sub-ry-pointer-writable x))
        (equal
         (sub-ry-pointer-zone x1)
         (sub-ry-pointer-zone x)))
       (sub-ry-all-open-states-p
        sx sy x y y1 x1))))))

(defun ntp4vc-pearl-multiprecision-sub-sub-sub-ryqtvc-statement
    (sy sx x y)
  (implies
   (and
    (sub-ry-background-p)
    (sub-ry-word32-p sy)
    (sub-ry-word32-p sx)
    (sub-ry-pointer-p x)
    (sub-ry-pointer-p y)
    (<= 0 (sub-ry-sint32 sy))
    (<= (sub-ry-sint32 sy)
        (sub-ry-sint32 sx))
    (sub-ry-valid-p
     x (sub-ry-sint32 sx))
    (sub-ry-valid-p
     y (sub-ry-sint32 sx))
    (equal
     (sub-ry-pointer-writable y)
     t))
   (and
    (sub-ry-valid-p
     y (sub-ry-sint32 sx))
    (sub-ry-valid-p
     x (sub-ry-sint32 sx))
    (<= 0 (sub-ry-sint32 sx))
    (<= (sub-ry-sint32 sx)
        (sub-ry-sint32 sx))
    (equal
     (sub-ry-pointer-writable y)
     t)
    (sub-ry-all-pointer-copies-p
     sx sy x y))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
