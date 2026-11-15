;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/add_Add_add_n_rxyqtvc: the verification condition for
;; doubling a multiprecision integer in place, including carry arithmetic,
;; pointer metadata preservation, and memory framing. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Fixed-width words are represented by their canonical unsigned integers.

(defun mpaddrxy-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mpaddrxy-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Exact two's-complement signed interpretation of a 32-bit word.

(defun mpaddrxy-signed32 (value)
  (if (< value 2147483648)
      value
    (- value 4294967296)))

(defun mpaddrxy-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

(defun mpaddrxy-bv64-list-p (values)
  (if (consp values)
      (and
       (mpaddrxy-bv64-p (car values))
       (mpaddrxy-bv64-list-p (cdr values)))
    (equal values nil)))

;; Pointers and zones remain arbitrary inhabited source carrier types.
;; Conservative stubs expose exactly the observations used by the VC, while
;; MPADDRXY-INTERFACE-P states all source typing conditions explicitly.

(defstub mpaddrxy-pointer-p (pointer) t)
(defstub mpaddrxy-zone-p (zone) t)
(defstub mpaddrxy-data (pointer) t)
(defstub mpaddrxy-offset (pointer) t)
(defstub mpaddrxy-minimum (pointer) t)
(defstub mpaddrxy-maximum (pointer) t)
(defstub mpaddrxy-writable (pointer) t)
(defstub mpaddrxy-zone (pointer) t)

(defun-sk mpaddrxy-pointer-domain-nonempty-p ()
  (exists (pointer)
    (mpaddrxy-pointer-p pointer)))

(defun-sk mpaddrxy-zone-domain-nonempty-p ()
  (exists (zone)
    (mpaddrxy-zone-p zone)))

(defun-sk mpaddrxy-interface-typed-p ()
  (forall (pointer)
    (implies
     (mpaddrxy-pointer-p pointer)
     (and
      (mpaddrxy-bv64-list-p
       (mpaddrxy-data pointer))
      (integerp
       (mpaddrxy-offset pointer))
      (integerp
       (mpaddrxy-minimum pointer))
      (integerp
       (mpaddrxy-maximum pointer))
      (booleanp
       (mpaddrxy-writable pointer))
      (mpaddrxy-zone-p
       (mpaddrxy-zone pointer))))))

(defun mpaddrxy-interface-p ()
  (and
   (mpaddrxy-pointer-domain-nonempty-p)
   (mpaddrxy-zone-domain-nonempty-p)
   (mpaddrxy-interface-typed-p)))

;; This is Int.toNat followed by total list indexing with the zero 64-bit word
;; as the default value.

(defun mpaddrxy-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun mpaddrxy-pelt (pointer index)
  (let* ((natural-index
          (mpaddrxy-int-to-nat index))
         (values
          (mpaddrxy-data pointer))
         (value
          (nth natural-index values)))
    (if (mpaddrxy-bv64-p value)
        value
      0)))

;; Little-endian radix-2^64 value of the indicated pointer prefix.

(defun mpaddrxy-value-from (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+
     (mpaddrxy-pelt pointer index)
     (*
      18446744073709551616
      (mpaddrxy-value-from
       pointer
       (+ index 1)
       (- count 1))))))

(defun mpaddrxy-value (pointer size)
  (mpaddrxy-value-from
   pointer
   (mpaddrxy-offset pointer)
   (mpaddrxy-int-to-nat size)))

(defun mpaddrxy-radix-power (exponent)
  (expt
   18446744073709551616
   (mpaddrxy-int-to-nat exponent)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpaddrxy-valid-p (pointer size)
  (and
   (mpaddrxy-pointer-p pointer)
   (mpaddrxy-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0
       (mpaddrxy-minimum pointer))
   (<= (mpaddrxy-minimum pointer)
       (mpaddrxy-offset pointer))
   (<= (+ (mpaddrxy-offset pointer)
          size)
       (mpaddrxy-maximum pointer))
   (<= (mpaddrxy-maximum pointer)
       (len (mpaddrxy-data pointer)))))

;; The universally quantified post-state has exactly the pointer observations
;; copied by the source VC.

(defun mpaddrxy-copy-fields-p (new old)
  (and
   (equal
    (len (mpaddrxy-data new))
    (len (mpaddrxy-data old)))
   (equal
    (mpaddrxy-offset new)
    (mpaddrxy-offset old))
   (equal
    (mpaddrxy-minimum new)
    (mpaddrxy-minimum old))
   (equal
    (mpaddrxy-maximum new)
    (mpaddrxy-maximum old))
   (equal
    (mpaddrxy-writable new)
    (mpaddrxy-writable old))
   (equal
    (mpaddrxy-zone new)
    (mpaddrxy-zone old))))

;; The memory outside [offset(new), offset(new)+size) is unchanged over the
;; source's full integer index domain.

(defun-sk mpaddrxy-frame-p (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index
          (mpaddrxy-offset new))
       (<= (+ (mpaddrxy-offset new)
              size)
           index))
      (equal
       (mpaddrxy-pelt new index)
       (mpaddrxy-pelt old index))))))

(defun mpaddrxy-core-postcondition-p
    (new old size result)
  (and
   (equal
    (+
     (mpaddrxy-value new size)
     (*
      (mpaddrxy-radix-power size)
      result))
    (+
     (mpaddrxy-value old size)
     (mpaddrxy-value old size)))
   (and
    (<= 0 result)
    (<= result 1))
   (mpaddrxy-frame-p
    new old size)))

(defun mpaddrxy-result-body-p
    (size-word old new result)
  (let ((size
         (mpaddrxy-signed32 size-word)))
    (implies
     (mpaddrxy-core-postcondition-p
      new old size result)
     (and
      (mpaddrxy-core-postcondition-p
       new old size result)
      (equal
       (mpaddrxy-minimum new)
       (mpaddrxy-minimum old))
      (equal
       (mpaddrxy-maximum new)
       (mpaddrxy-maximum old))
      (equal
       (len (mpaddrxy-data new))
       (len (mpaddrxy-data old)))))))

(defun-sk mpaddrxy-all-results-p
    (size-word old new)
  (forall (result)
    (implies
     (mpaddrxy-bv64-p result)
     (mpaddrxy-result-body-p
      size-word old new result))))

(defun mpaddrxy-post-state-body-p
    (size-word old new)
  (implies
   (mpaddrxy-copy-fields-p new old)
   (mpaddrxy-all-results-p
    size-word old new)))

(defun-sk mpaddrxy-all-post-states-p
    (size-word old)
  (forall (new)
    (implies
     (mpaddrxy-pointer-p new)
     (mpaddrxy-post-state-body-p
      size-word old new))))

(defun-sk
    ntp4vc-pearl-multiprecision-add-add-add-n-rxyqtvc-statement
    ()
  (forall (size-word pointer)
    (implies
     (and
      (mpaddrxy-interface-p)
      (mpaddrxy-bv32-p size-word)
      (mpaddrxy-pointer-p pointer)
      (<= 0
          (mpaddrxy-signed32 size-word))
      (equal
       (mpaddrxy-writable pointer)
       t)
      (mpaddrxy-valid-p
       pointer
       (mpaddrxy-signed32 size-word)))
     (and
      (<= 0
          (mpaddrxy-signed32 size-word))
      (mpaddrxy-valid-p
       pointer
       (mpaddrxy-signed32 size-word))
      (equal
       (mpaddrxy-writable pointer)
       t)
      (mpaddrxy-all-post-states-p
       size-word pointer)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
