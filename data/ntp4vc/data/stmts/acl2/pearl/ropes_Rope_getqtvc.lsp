;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/ropes_Rope_getqtvc: the rope character-access verification condition,
;; preserving rope invariants, recursive branch bounds, and agreement with the
;; indexed character of the modeled string. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; The source character and immutable-string types are arbitrary inhabited
;; carriers. These conservative interfaces provide the fixed operations from
;; the imported MyString theory; every typing and mathematical law used by the
;; theory remains an explicit premise of the statement.

(defstub rrg-char-p (x) t)
(defstub rrg-char-string-p (x) t)
(defstub rrg-dummy-char () t)
(defstub rrg-ms-empty () t)
(defstub rrg-ms-length (s) t)
(defstub rrg-ms-index (s i) t)
(defstub rrg-ms-app (s1 s2) t)
(defstub rrg-ms-sub (s ofs len) t)

(defun-sk rrg-length-typed-p ()
  (forall (s)
    (implies
     (rrg-char-string-p s)
     (and
      (integerp (rrg-ms-length s))
      (<= 0 (rrg-ms-length s))))))

(defun-sk rrg-index-typed-p ()
  (forall (s i)
    (implies
     (and
      (rrg-char-string-p s)
      (integerp i))
     (rrg-char-p (rrg-ms-index s i)))))

(defun-sk rrg-app-typed-p ()
  (forall (s1 s2)
    (implies
     (and
      (rrg-char-string-p s1)
      (rrg-char-string-p s2))
     (rrg-char-string-p
      (rrg-ms-app s1 s2)))))

(defun-sk rrg-sub-typed-p ()
  (forall (s ofs len)
    (implies
     (and
      (rrg-char-string-p s)
      (integerp ofs)
      (integerp len))
     (rrg-char-string-p
      (rrg-ms-sub s ofs len)))))

(defun-sk rrg-string-pointwise-equal-p (s1 s2)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i (rrg-ms-length s1)))
      (equal
       (rrg-ms-index s1 i)
       (rrg-ms-index s2 i))))))

(defun-sk rrg-extensionality-law-p ()
  (forall (s1 s2)
    (implies
     (and
      (rrg-char-string-p s1)
      (rrg-char-string-p s2))
     (implies
      (and
       (equal
        (rrg-ms-length s1)
        (rrg-ms-length s2))
       (rrg-string-pointwise-equal-p s1 s2))
      (equal s1 s2)))))

(defun-sk rrg-app-length-law-p ()
  (forall (s1 s2)
    (implies
     (and
      (rrg-char-string-p s1)
      (rrg-char-string-p s2))
     (equal
      (rrg-ms-length (rrg-ms-app s1 s2))
      (+
       (rrg-ms-length s1)
       (rrg-ms-length s2))))))

(defun-sk rrg-app-left-index-law-p ()
  (forall (s1 s2 i)
    (implies
     (and
      (rrg-char-string-p s1)
      (rrg-char-string-p s2)
      (integerp i))
     (implies
      (and
       (<= 0 i)
       (< i (rrg-ms-length s1)))
      (equal
       (rrg-ms-index
        (rrg-ms-app s1 s2)
        i)
       (rrg-ms-index s1 i))))))

(defun-sk rrg-app-right-index-law-p ()
  (forall (s1 s2 i)
    (implies
     (and
      (rrg-char-string-p s1)
      (rrg-char-string-p s2)
      (integerp i))
     (implies
      (and
       (<= (rrg-ms-length s1) i)
       (< i
          (+
           (rrg-ms-length s1)
           (rrg-ms-length s2))))
      (equal
       (rrg-ms-index
        (rrg-ms-app s1 s2)
        i)
       (rrg-ms-index
        s2
        (- i (rrg-ms-length s1))))))))

(defun-sk rrg-sub-length-law-p ()
  (forall (s ofs len)
    (implies
     (and
      (rrg-char-string-p s)
      (integerp ofs)
      (integerp len))
     (implies
      (and
       (<= 0 len)
       (<= 0 ofs)
       (<= ofs (rrg-ms-length s))
       (<= (+ ofs len)
           (rrg-ms-length s)))
      (equal
       (rrg-ms-length
        (rrg-ms-sub s ofs len))
       len)))))

(defun-sk rrg-sub-index-law-p ()
  (forall (s ofs len i)
    (implies
     (and
      (rrg-char-string-p s)
      (integerp ofs)
      (integerp len)
      (integerp i))
     (implies
      (and
       (<= 0 len)
       (<= 0 ofs)
       (<= ofs (rrg-ms-length s))
       (<= (+ ofs len)
           (rrg-ms-length s))
       (<= 0 i)
       (< i len))
      (equal
       (rrg-ms-index
        (rrg-ms-sub s ofs len)
        i)
       (rrg-ms-index s (+ ofs i)))))))

(defun rrg-mystring-background-p ()
  (and
   (rrg-char-p (rrg-dummy-char))
   (rrg-char-string-p (rrg-ms-empty))
   (rrg-length-typed-p)
   (rrg-index-typed-p)
   (rrg-app-typed-p)
   (rrg-sub-typed-p)
   (equal (rrg-ms-length (rrg-ms-empty)) 0)
   (rrg-extensionality-law-p)
   (rrg-app-length-law-p)
   (rrg-app-left-index-law-p)
   (rrg-app-right-index-law-p)
   (rrg-sub-length-law-p)
   (rrg-sub-index-law-p)))

;; Ropes are the exact finite inductive datatype from the source:
;; Emp, Str(string, offset, length), and App(left, right, stored length).

(defun rrg-str-shape-p (rope)
  (and
   (true-listp rope)
   (equal (len rope) 4)
   (equal (car rope) :rrg-str)))

(defun rrg-app-shape-p (rope)
  (and
   (true-listp rope)
   (equal (len rope) 4)
   (equal (car rope) :rrg-app)))

(defun rrg-str-string (rope)
  (cadr rope))

(defun rrg-str-offset (rope)
  (caddr rope))

(defun rrg-str-length (rope)
  (cadddr rope))

(defun rrg-app-left (rope)
  (cadr rope))

(defun rrg-app-right (rope)
  (caddr rope))

(defun rrg-app-length (rope)
  (cadddr rope))

(defun rrg-rope-p (rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond
   ((equal rope :rrg-emp)
    t)
   ((rrg-str-shape-p rope)
    (and
     (rrg-char-string-p
      (rrg-str-string rope))
     (integerp
      (rrg-str-offset rope))
     (integerp
      (rrg-str-length rope))))
   ((rrg-app-shape-p rope)
    (and
     (rrg-rope-p
      (rrg-app-left rope))
     (rrg-rope-p
      (rrg-app-right rope))
     (integerp
      (rrg-app-length rope))))
   (t nil)))

(defun rrg-rope-length (rope)
  (cond
   ((equal rope :rrg-emp)
    0)
   ((rrg-str-shape-p rope)
    (rrg-str-length rope))
   ((rrg-app-shape-p rope)
    (rrg-app-length rope))
   (t 0)))

(defun rrg-rope-inv-p (rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond
   ((equal rope :rrg-emp)
    t)
   ((rrg-str-shape-p rope)
    (let ((s (rrg-str-string rope))
          (ofs (rrg-str-offset rope))
          (len (rrg-str-length rope)))
      (and
       (< 0 len)
       (<= 0 ofs)
       (< ofs (rrg-ms-length s))
       (<= (+ ofs len)
           (rrg-ms-length s)))))
   ((rrg-app-shape-p rope)
    (let ((left (rrg-app-left rope))
          (right (rrg-app-right rope))
          (stored-length
           (rrg-app-length rope)))
      (and
       (< 0 (rrg-rope-length left))
       (rrg-rope-inv-p left)
       (< 0 (rrg-rope-length right))
       (rrg-rope-inv-p right)
       (equal
        stored-length
        (+
         (rrg-rope-length left)
         (rrg-rope-length right))))))
   (t nil)))

(defun rrg-rope-string (rope)
  (declare (xargs :measure (acl2-count rope)))
  (cond
   ((equal rope :rrg-emp)
    (rrg-ms-empty))
   ((rrg-str-shape-p rope)
    (rrg-ms-sub
     (rrg-str-string rope)
     (rrg-str-offset rope)
     (rrg-str-length rope)))
   ((rrg-app-shape-p rope)
    (rrg-ms-app
     (rrg-rope-string
      (rrg-app-left rope))
     (rrg-rope-string
      (rrg-app-right rope))))
   (t
    (rrg-ms-empty))))

;; This preserves the first source match expression, including the repeated
;; match on the original App node and each recursive-call bound.

(defun rrg-branch-bounds-p (rope i)
  (cond
   ((equal rope :rrg-emp)
    nil)
   ((rrg-str-shape-p rope)
    (let ((offset-index
           (+ (rrg-str-offset rope) i)))
      (and
       (<= 0 offset-index)
       (< offset-index
          (rrg-ms-length
           (rrg-str-string rope))))))
   ((rrg-app-shape-p rope)
    (let* ((left (rrg-app-left rope))
           (right (rrg-app-right rope))
           (left-length
            (rrg-rope-length left)))
      (if (< i left-length)
          (and
           (or
            (equal
             (rrg-app-left rope)
             left)
            (equal
             (rrg-app-right rope)
             left))
           (rrg-rope-inv-p left)
           (<= 0 i)
           (< i
              (rrg-rope-length left)))
        (let ((right-index
               (- i left-length)))
          (and
           (or
            (equal
             (rrg-app-left rope)
             right)
            (equal
             (rrg-app-right rope)
             right))
           (rrg-rope-inv-p right)
           (<= 0 right-index)
           (< right-index
              (rrg-rope-length right)))))))
   (t nil)))

;; This is the source branch equation that characterizes a possible result of
;; the recursive get computation.

(defun rrg-result-premise-p (rope i result)
  (cond
   ((equal rope :rrg-emp)
    nil)
   ((rrg-str-shape-p rope)
    (equal
     result
     (rrg-ms-index
      (rrg-str-string rope)
      (+ (rrg-str-offset rope) i))))
   ((rrg-app-shape-p rope)
    (let* ((left (rrg-app-left rope))
           (right (rrg-app-right rope))
           (left-length
            (rrg-rope-length left)))
      (if (< i left-length)
          (equal
           result
           (rrg-ms-index
            (rrg-rope-string left)
            i))
        (equal
         result
         (rrg-ms-index
          (rrg-rope-string right)
          (- i left-length))))))
   (t nil)))

;; RESULT remains universally quantified over the full abstract character
;; carrier inside the conclusion, exactly as in the source VC.

(defun-sk rrg-all-results-p (rope i)
  (forall (result)
    (implies
     (rrg-char-p result)
     (implies
      (rrg-result-premise-p
       rope i result)
      (equal
       result
       (rrg-ms-index
        (rrg-rope-string rope)
        i))))))

(defun-sk
  ntp4vc-pearl-ropes-rope-getqtvc-statement
  ()
  (forall (rope i)
    (implies
     (and
      (rrg-mystring-background-p)
      (rrg-rope-p rope)
      (integerp i)
      (rrg-rope-inv-p rope)
      (<= 0 i)
      (< i (rrg-rope-length rope)))
     (and
      (rrg-branch-bounds-p rope i)
      (rrg-all-results-p rope i)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
