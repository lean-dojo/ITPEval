;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/powm_Powm_redcifyqtvc: the verification condition for
;; converting a multiprecision integer to Montgomery-reduced form via
;; zero-extension, copying, and quotient-remainder division.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defconst *redq-radix* 18446744073709551616)

;; Canonical integers in [0, 2^w) represent the source fixed-width words.

(defun redq-bv32-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 4294967296)))

(defun redq-bv64-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word *redq-radix*)))

(defun redq-sint32 (word)
  (if (< word 2147483648)
      word
    (- word 4294967296)))

(defun redq-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Pointers and zones remain arbitrary inhabited source carriers.  The
;; conservative selectors expose exactly the observations occurring in the
;; verification condition, with all source typing requirements explicit.

(defstub redq-pointer-p (pointer) t)
(defstub redq-zone-p (zone) t)
(defstub redq-data (pointer) t)
(defstub redq-offset (pointer) t)
(defstub redq-minimum (pointer) t)
(defstub redq-maximum (pointer) t)
(defstub redq-writable (pointer) t)
(defstub redq-zone (pointer) t)

(defun redq-bv64-list-p (values)
  (if (consp values)
      (and
       (redq-bv64-p (car values))
       (redq-bv64-list-p (cdr values)))
    (equal values nil)))

(defun-sk redq-pointer-domain-nonempty-p ()
  (exists (pointer)
    (redq-pointer-p pointer)))

(defun-sk redq-pointer-selectors-typed-p ()
  (forall (pointer)
    (implies
     (redq-pointer-p pointer)
     (and
      (redq-bv64-list-p
       (redq-data pointer))
      (integerp (redq-offset pointer))
      (integerp (redq-minimum pointer))
      (integerp (redq-maximum pointer))
      (booleanp (redq-writable pointer))
      (redq-zone-p
       (redq-zone pointer))))))

(defun redq-interface-p ()
  (and
   (redq-pointer-domain-nonempty-p)
   (redq-pointer-selectors-typed-p)))

;; Int.toNat sends negative integers to zero.  Total list access uses the
;; canonical inhabited default 64-bit word zero outside the represented data.

(defun redq-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun redq-pelt (pointer index)
  (let ((word
         (nth
          (redq-int-to-nat index)
          (redq-data pointer))))
    (if (redq-bv64-p word)
        word
      0)))

(defun redq-plength (pointer)
  (len (redq-data pointer)))

;; This is mach.c.C.valid with the signed-32 size bound expanded.

(defun redq-valid-p (pointer size)
  (and
   (redq-pointer-p pointer)
   (redq-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (redq-minimum pointer))
   (<= (redq-minimum pointer)
       (redq-offset pointer))
   (<= (+ (redq-offset pointer) size)
       (redq-maximum pointer))
   (<= (redq-maximum pointer)
       (redq-plength pointer))))

;; Little-endian base-2^64 value of a pointer interval.

(defun redq-value-count (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp (nfix count))
      0
    (+
     (redq-pelt pointer index)
     (*
      *redq-radix*
      (redq-value-count
       pointer
       (+ index 1)
       (- (nfix count) 1))))))

(defun redq-value (pointer size)
  (redq-value-count
   pointer
   (redq-offset pointer)
   size))

(defun redq-ipow (base exponent)
  (expt base (nfix exponent)))

(defun redq-redc-p (ur u n modulus)
  (equal
   (mod ur modulus)
   (mod
    (* (redq-ipow *redq-radix* n)
       u)
    modulus)))

;; Extensional equality of the source integer-indexed pelts maps.

(defun-sk redq-same-pelts-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (redq-pelt left index)
      (redq-pelt right index)))))

(defun redq-same-metadata-p (left right)
  (and
   (equal (redq-plength left)
          (redq-plength right))
   (equal (redq-offset left)
          (redq-offset right))
   (equal (redq-minimum left)
          (redq-minimum right))
   (equal (redq-maximum left)
          (redq-maximum right))
   (equal (redq-writable left)
          (redq-writable right))
   (equal (redq-zone left)
          (redq-zone right))))

(defun-sk redq-unchanged-outside-p
    (new old start size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index start)
       (<= (+ start size) index))
      (equal
       (redq-pelt new index)
       (redq-pelt old index))))))

(defun-sk redq-map-eq-sub-shift-p
    (left right left-start right-start size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index size))
      (equal
       (redq-pelt left
                  (+ left-start index))
       (redq-pelt right
                  (+ right-start index)))))))

(defun redq-allocation-description-p
    (pointer size)
  (and
   (equal (redq-plength pointer) size)
   (equal (redq-offset pointer) 0)
   (equal (redq-minimum pointer) 0)
   (equal (redq-maximum pointer) size)
   (equal (redq-writable pointer) t)))

;; Final quotient-remainder continuation.

(defun redq-division-result-p
    (n mp o7 qp1 rp1 tp2)
  (and
   (equal
    (redq-value tp2 (redq-sint32 o7))
    (+
     (*
      (redq-value
       qp1
       (+ (- (redq-sint32 o7)
             (redq-sint32 n))
          1))
      (redq-value mp (redq-sint32 n)))
     (redq-value rp1 (redq-sint32 n))))
   (<
    (redq-value rp1 (redq-sint32 n))
    (redq-value mp (redq-sint32 n)))))

(defun redq-qp1-rp1-case-p
    (rp n up un mp qp tp2 o7 qp1 rp1)
  (implies
   (redq-same-metadata-p qp1 qp)
   (implies
    (redq-same-metadata-p rp1 rp)
    (implies
     (redq-division-result-p
      n mp o7 qp1 rp1 tp2)
     (and
      (equal
       (redq-value rp1 (redq-sint32 n))
       (mod
        (*
         (redq-ipow
          *redq-radix*
          (redq-sint32 n))
         (redq-value up (redq-sint32 un)))
        (redq-value mp (redq-sint32 n))))
      (redq-redc-p
       (redq-value rp1 (redq-sint32 n))
       (redq-value up (redq-sint32 un))
       (redq-sint32 n)
       (redq-value mp (redq-sint32 n))))))))

(defun-sk redq-all-qp1-rp1-p
    (rp n up un mp qp tp2 o7)
  (forall (qp1 rp1)
    (implies
     (and
      (redq-pointer-p qp1)
      (redq-pointer-p rp1))
     (redq-qp1-rp1-case-p
      rp n up un mp qp tp2 o7 qp1 rp1))))

(defun redq-o7-body-p
    (rp n up un mp qp tp2 o7)
  (implies
   (equal
    (redq-sint32 o7)
    (+ (redq-sint32 un)
       (redq-sint32 n)))
   (and
    (and
     (<= 1 (redq-sint32 n))
     (<= (redq-sint32 n)
         (redq-sint32 o7))
     (<= (redq-sint32 o7)
         (- 2147483647 1)))
    (redq-valid-p tp2 (redq-sint32 o7))
    (redq-valid-p mp (redq-sint32 n))
    (redq-valid-p
     qp
     (+ (- (redq-sint32 o7)
           (redq-sint32 n))
        1))
    (redq-valid-p rp (redq-sint32 n))
    (and
     (equal (redq-writable qp) t)
     (equal (redq-writable rp) t))
    (<
     0
     (redq-pelt
      mp
      (+
       (redq-offset mp)
       (redq-sint32 n)
       -1)))
    (redq-all-qp1-rp1-p
     rp n up un mp qp tp2 o7))))

(defun-sk redq-all-o7-p
    (rp n up un mp qp tp2)
  (forall (o7)
    (implies
     (redq-bv32-p o7)
     (redq-o7-body-p
      rp n up un mp qp tp2 o7))))

;; Continuation after copying UP into the shifted suffix O6 of TP2.

(defun redq-o6-first-state-p
    (o5 o6 tp2)
  (and
   (equal (redq-data o6)
          (redq-data tp2))
   (equal (redq-plength tp2)
          (redq-plength o5))
   (equal (redq-offset o6)
          (redq-offset o5))
   (equal (redq-minimum o6)
          (redq-minimum o5))
   (equal (redq-maximum o6)
          (redq-maximum o5))
   (equal (redq-writable o6)
          (redq-writable o5))
   (equal (redq-zone o6)
          (redq-zone o5))))

(defun redq-o6-tp2-case-p
    (rp n up un mp qp tp1 o5 o6 tp2)
  (implies
   (redq-o6-first-state-p o5 o6 tp2)
   (implies
    (redq-same-metadata-p tp2 tp1)
    (implies
     (and
      (redq-map-eq-sub-shift-p
       o6
       up
       (redq-offset o6)
       (redq-offset up)
       (redq-sint32 un))
      (redq-unchanged-outside-p
       o6
       o5
       (redq-offset o6)
       (redq-sint32 un)))
     (and
      (redq-int32-in-bounds-p
       (+ (redq-sint32 un)
          (redq-sint32 n)))
      (redq-all-o7-p
       rp n up un mp qp tp2))))))

(defun-sk redq-all-o6-tp2-p
    (rp n up un mp qp tp1 o5)
  (forall (o6 tp2)
    (implies
     (and
      (redq-pointer-p o6)
      (redq-pointer-p tp2))
     (redq-o6-tp2-case-p
      rp n up un mp qp tp1 o5 o6 tp2))))

(defun redq-o5-state-p
    (tp1 n o5)
  (and
   (equal
    (redq-offset o5)
    (+ (redq-offset tp1)
       (redq-sint32 n)))
   (equal (redq-plength o5)
          (redq-plength tp1))
   (redq-same-pelts-p o5 tp1)
   (equal (redq-data o5)
          (redq-data tp1))
   (equal (redq-minimum o5)
          (redq-minimum tp1))
   (equal (redq-maximum o5)
          (redq-maximum tp1))
   (equal (redq-zone o5)
          (redq-zone tp1))
   (equal (redq-writable o5)
          (redq-writable tp1))))

(defun redq-o5-body-p
    (rp n up un mp qp tp1 o5)
  (implies
   (redq-o5-state-p tp1 n o5)
   (and
    (and
     (redq-valid-p up (redq-sint32 un))
     (redq-valid-p o5 (redq-sint32 un))
     (equal (redq-writable o5) t))
    (redq-all-o6-tp2-p
     rp n up un mp qp tp1 o5))))

(defun-sk redq-all-o5-p
    (rp n up un mp qp tp1)
  (forall (o5)
    (implies
     (redq-pointer-p o5)
     (redq-o5-body-p
      rp n up un mp qp tp1 o5))))

;; Continuation after zeroing the first N limbs of TP.

(defun redq-tp1-body-p
    (rp n up un mp qp tp tp1)
  (implies
   (redq-same-metadata-p tp1 tp)
   (implies
    (and
     (equal
      (redq-value tp1 (redq-sint32 n))
      0)
     (redq-unchanged-outside-p
      tp1
      tp
      (redq-offset tp1)
      (redq-sint32 n)))
    (and
     (and
      (<= (redq-minimum tp1)
          (+ (redq-offset tp1)
             (redq-sint32 n)))
      (<= (+ (redq-offset tp1)
             (redq-sint32 n))
          (redq-maximum tp1)))
     (redq-all-o5-p
      rp n up un mp qp tp1)))))

(defun-sk redq-all-tp1-p
    (rp n up un mp qp tp)
  (forall (tp1)
    (implies
     (redq-pointer-p tp1)
     (redq-tp1-body-p
      rp n up un mp qp tp tp1))))

(defun redq-qp-body-p
    (rp n up un mp tp o4 qp)
  (implies
   (redq-allocation-description-p qp o4)
   (and
    (and
     (redq-valid-p tp (redq-sint32 n))
     (equal (redq-writable tp) t))
    (redq-all-tp1-p
     rp n up un mp qp tp))))

(defun-sk redq-all-qp-p
    (rp n up un mp tp o4)
  (forall (qp)
    (implies
     (redq-pointer-p qp)
     (redq-qp-body-p
      rp n up un mp tp o4 qp))))

(defun redq-o4-body-p
    (rp n up un mp tp o3 o4)
  (implies
   (equal o4 (redq-sint32 o3))
   (and
    (<= 0 o4)
    (redq-all-qp-p
     rp n up un mp tp o4))))

(defun-sk redq-all-o4-p
    (rp n up un mp tp o3)
  (forall (o4)
    (implies
     (redq-bv32-p o4)
     (redq-o4-body-p
      rp n up un mp tp o3 o4))))

(defun redq-o3-body-p
    (rp n up un mp tp o3)
  (implies
   (equal
    (redq-sint32 o3)
    (+ (redq-sint32 un) 1))
   (and
    (<= 0 (redq-sint32 o3))
    (redq-all-o4-p
     rp n up un mp tp o3))))

(defun-sk redq-all-o3-p
    (rp n up un mp tp)
  (forall (o3)
    (implies
     (redq-bv32-p o3)
     (redq-o3-body-p
      rp n up un mp tp o3))))

(defun redq-tp-body-p
    (rp n up un mp o2 tp)
  (implies
   (redq-allocation-description-p tp o2)
   (and
    (redq-int32-in-bounds-p
     (+ (redq-sint32 un) 1))
    (redq-all-o3-p
     rp n up un mp tp))))

(defun-sk redq-all-tp-p
    (rp n up un mp o2)
  (forall (tp)
    (implies
     (redq-pointer-p tp)
     (redq-tp-body-p
      rp n up un mp o2 tp))))

(defun redq-o2-body-p
    (rp n up un mp o1 o2)
  (implies
   (equal o2 (redq-sint32 o1))
   (and
    (<= 0 o2)
    (redq-all-tp-p
     rp n up un mp o2))))

(defun-sk redq-all-o2-p
    (rp n up un mp o1)
  (forall (o2)
    (implies
     (redq-bv32-p o2)
     (redq-o2-body-p
      rp n up un mp o1 o2))))

(defun redq-o1-body-p
    (rp n up un mp o1)
  (implies
   (equal
    (redq-sint32 o1)
    (+ (redq-sint32 un)
       (redq-sint32 n)))
   (and
    (<= 0 (redq-sint32 o1))
    (redq-all-o2-p
     rp n up un mp o1))))

(defun-sk redq-all-o1-p
    (rp n up un mp)
  (forall (o1)
    (implies
     (redq-bv32-p o1)
     (redq-o1-body-p
      rp n up un mp o1))))

(defun
    ntp4vc-pearl-multiprecision-powm-powm-redcifyqtvc-statement
    (rp n up un mp)
  (implies
   (and
    (redq-interface-p)
    (redq-pointer-p rp)
    (redq-bv32-p n)
    (redq-pointer-p up)
    (redq-bv32-p un)
    (redq-pointer-p mp)
    (redq-valid-p rp (redq-sint32 n))
    (redq-valid-p up (redq-sint32 un))
    (redq-valid-p mp (redq-sint32 n))
    (<= 1 (redq-sint32 n))
    (<= 1 (redq-sint32 un))
    (< (+ (redq-sint32 un)
          (redq-sint32 n))
       2147483647)
    (<
     0
     (redq-pelt
      mp
      (+
       (redq-offset mp)
       (redq-sint32 n)
       -1)))
    (equal (redq-writable rp) t))
   (and
    (redq-int32-in-bounds-p
     (+ (redq-sint32 un)
        (redq-sint32 n)))
    (redq-all-o1-p rp n up un mp))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
