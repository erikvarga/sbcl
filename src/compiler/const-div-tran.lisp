;;;; Transforms specific to division when the divisor is a known constant

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!C")

;;; Note that all the integer division functions are available for
;;; inline expansion.

(macrolet ((deffrob (fun)
             `(define-source-transform ,fun (x &optional (y nil y-p))
                (declare (ignore y))
                (if y-p
                    (values nil t)
                    `(,',fun ,x 1)))))
  (deffrob truncate)
  (deffrob round)
  #-sb-xc-host ; (See CROSS-FLOAT-INFINITY-KLUDGE.)
  (deffrob floor)
  #-sb-xc-host ; (See CROSS-FLOAT-INFINITY-KLUDGE.)
  (deffrob ceiling))


;;;; converting special case divide to shifts

;;; These must come before the ones below, so that they are tried
;;; first.
(deftransform floor ((number divisor))
  `(multiple-value-bind (tru rem) (truncate number divisor)
     (if (and (not (zerop rem))
              (if (minusp divisor)
                  (plusp number)
                  (minusp number)))
         (values (1- tru) (+ rem divisor))
         (values tru rem))))

(deftransform ceiling ((number divisor))
  `(multiple-value-bind (tru rem) (truncate number divisor)
     (if (and (not (zerop rem))
              (if (minusp divisor)
                  (minusp number)
                  (plusp number)))
         (values (+ tru 1) (- rem divisor))
         (values tru rem))))

(deftransform rem ((number divisor))
  `(nth-value 1 (truncate number divisor)))

(deftransform mod ((number divisor))
  `(let ((rem (rem number divisor)))
     (if (and (not (zerop rem))
              (if (minusp divisor)
                  (plusp number)
                  (minusp number)))
         (+ rem divisor)
         rem))
)

;;; If arg is a constant power of two, turn FLOOR into a shift and
;;; mask. If CEILING, do FLOOR and correct the remainder and
;;; quotient.
(flet ((frob (y ceil-p)
         (unless (constant-lvar-p y)
           (give-up-ir1-transform))
         (let* ((y (lvar-value y))
                (y-abs (abs y))
                (len (1- (integer-length y-abs))))
           (unless (and (> y-abs 0) (= y-abs (ash 1 len)))
             (give-up-ir1-transform))
           (let ((shift (- len))
                 (mask (1- y-abs))
                 (delta (if ceil-p y 0)))
             (if (minusp y)
                  `(let ((rem (- (logand (- x) ,mask))))
                     (values (- ,(if ceil-p '(if (zerop rem) 0 1) 0)
                                (+ (ash x ,shift)
                                   (if (zerop rem) 0 1)))
                             (- rem (if (zerop rem) 0 ,delta))))
                  `(let ((rem (logand x ,mask)))
                     (values (+ (ash x ,shift)
                                ,(if ceil-p '(if (zerop rem) 0 1) 0))
                             (- rem (if (zerop rem) 0 ,delta)))))))))
  (deftransform floor ((x y) (integer integer) *)
    "convert division by 2^k to shift"
    (frob y nil))
  (deftransform ceiling ((x y) (integer integer) *)
    "convert division by 2^k to shift"
    (frob y t)))

;;; Do the same for MOD.
(deftransform mod ((x y) (integer integer) *)
  "convert remainder mod 2^k to LOGAND"
  (unless (constant-lvar-p y)
    (give-up-ir1-transform))
  (let* ((y (lvar-value y))
         (y-abs (abs y))
         (len (1- (integer-length y-abs))))
    (unless (and (> y-abs 0) (= y-abs (ash 1 len)))
      (give-up-ir1-transform))
    (let ((mask (1- y-abs)))
      (if (minusp y)
          `(- (logand (- x) ,mask))
          `(logand x ,mask)))))

;;; If arg is a constant power of two, turn TRUNCATE into a shift and mask.
(deftransform truncate ((x y) (integer integer))
  "convert division by 2^k to shift"
  (unless (constant-lvar-p y)
    (give-up-ir1-transform))
  (let* ((y (lvar-value y))
         (y-abs (abs y))
         (len (1- (integer-length y-abs))))
    (unless (and (> y-abs 0) (= y-abs (ash 1 len)))
      (give-up-ir1-transform))
    (let* ((shift (- len))
           (mask (1- y-abs))
           (x-type (lvar-type x))
           (max-x  (or (and (numeric-type-p x-type)
                            (numeric-type-high x-type)) '*))
           (min-x  (or (and (numeric-type-p x-type)
                            (numeric-type-low x-type)) '*))
           (quot
            `(ash
              (truly-the (integer ,min-x ,max-x)
                         (+ x (if (minusp x) ,(1- y-abs) 0)))
              ,shift)))
      (when (minusp y) (setq quot `(- ,quot)))
      `(if (minusp x)
           (values ,quot
                   (- (logand (- x) ,mask)))
           (values ,quot
                   (logand x ,mask))))))

;;; And the same for REM.
(deftransform rem ((x y) (integer integer) *)
  "convert remainder mod 2^k to LOGAND"
  (unless (constant-lvar-p y)
    (give-up-ir1-transform))
  (let* ((y (lvar-value y))
         (y-abs (abs y))
         (len (1- (integer-length y-abs))))
    (unless (and (> y-abs 0) (= y-abs (ash 1 len)))
      (give-up-ir1-transform))
    (let ((mask (1- y-abs)))
      `(if (minusp x)
           (- (logand (- x) ,mask))
           (logand x ,mask)))))


;;;; converting division to multiplication, addition, shift, etc.

;;; Get the multiply-high multiplier that can be used instead of
;;; dividing by y. Used in gen-(un)signed-div-by-constant-expr
(defun choose-multiplier (y precision)
  (do* ((l (integer-length (1- y)))
        (shift l (1- shift))
        (expt-2-n+l (expt 2 (+ sb!vm:n-word-bits l)))
        (m-low (truncate expt-2-n+l y) (ash m-low -1))
        (m-high (truncate (+ expt-2-n+l
                             (ash expt-2-n+l (- precision)))
                          y)
                (ash m-high -1)))
       ((not (and (< (ash m-low -1) (ash m-high -1))
                  (> shift 0)))
        (values m-high shift))))

;;; Get the direct multiplier that can be used instead of
;;; dividing by y. Used in gen-(un)signed-div-by-constant-expr
(defun choose-direct-multiplier (y max-x)
  (let* ((max-shift (+ (integer-length max-x) (integer-length y)))
         (scale (ash 1 max-shift))
         (low (floor scale y))
         (k (1- (ceiling scale max-x)))
         (high (floor (+ scale k) y))
         (diff (logxor low high))
         (delta (1- (integer-length diff))))
    (values (ash high (- delta)) (- max-shift delta))))

;;; Return an expression to calculate the integer quotient of X and
;;; constant Y, using multiplication, shift and add/sub instead of
;;; division. Both arguments must be unsigned, fit in a machine word and
;;; Y must neither be zero nor a power of two. The quotient is rounded
;;; towards zero.
;;; The algorithm is taken from the paper "Division by Invariant
;;; Integers using Multiplication", 1994 by Torbj\"{o}rn Granlund and
;;; Peter L. Montgomery, Figures 4.2 and 6.2, modified to exclude the
;;; case of division by powers of two.
;;; It is sometimes possible that all intermediate values fit in the
;;; word boundary, so there is no need to use multiply-high.  In these
;;; cases, use multiplication and shifting directly.
;;; The algorithm includes an adaptive precision argument.  Use it, since
;;; we often have sub-word value ranges.  Careful, in this case, we need
;;; p s.t 2^p > n, not the ceiling of the binary log.
;;; Also, for some reason, the paper prefers shifting to masking.  Mask
;;; instead.  Masking is equivalent to shifting right, then left again;
;;; all the intermediate values are still words, so we just have to shift
;;; right a bit more to compensate, at the end.
;;; Before resorting to multiplying by an n+1 bit constant, check if X+1
;;; still fits in n bits, and if so, use instead the multiply-add method
;;; described in the paper "N-Bit Unsigned Division Via N-Bit Multiply-Add",
;;; 2005 by Arch D. Robison.  Once again, use multiply-high only if
;;; multiplication and shifting cannot be done directly.
(defun gen-unsigned-div-by-constant-expr (y max-x)
  (declare (type (integer 3 #.most-positive-word) y)
           (type word max-x))
  (aver (not (zerop (logand y (1- y)))))
  (flet ((ld (x)
             ;; the floor of the binary logarithm of (positive) X
             (integer-length (1- x))))
    (let ((n (expt 2 sb!vm:n-word-bits))
          (precision (integer-length max-x))
          (shift1 0))
      (multiple-value-bind (m shift2)
          (choose-direct-multiplier y max-x)
        (cond
          ((< (* max-x m) n)
           `(ash (* x ,m) ,(- shift2)))
          (t
           (multiple-value-setq (m shift2)
             (choose-multiplier y precision))
           (when (and (>= m n) (evenp y))
             (setq shift1 (ld (logand y (- y))))
             (multiple-value-setq (m shift2)
               (choose-multiplier (/ y (ash 1 shift1))
                                  (- precision shift1))))
           (cond ((>= m n)
                  (cond ((< max-x (1- n))
                         (let* ((shift
                                (+ (integer-length max-x) (integer-length y) -1))
                               (m (floor (ash 1 shift) y)))
                           (cond ((< (* (1+ max-x) m) n)
                                  `(ash (* (+1 x) ,m) ,(- shift)))
                                 (t
                                  (let ((scale
                                         (max 0 (- sb!vm:n-word-bits shift))))
                                    `(ash (%multiply-high (1+ x)
                                                          ,(ash m scale))
                                          ,(- sb!vm:n-word-bits shift scale)))))))
                        (t
                         (flet ((word (x)
                                  `(truly-the word ,x)))
                           `(let* ((num x)
                                   (t1 (%multiply-high num ,(- m n))))
                              (ash ,(word `(+ t1 (ash ,(word `(- num t1))
                                                      -1)))
                                   ,(- 1 shift2)))))))
                 ((and (zerop shift1) (zerop shift2))
                  (let ((max (truncate max-x y)))
                    ;; Explicit TRULY-THE needed to get the FIXNUM=>FIXNUM
                    ;; VOP.
                    `(truly-the (integer 0 ,max)
                                (%multiply-high x ,m))))
                 (t
                  `(ash (%multiply-high (logandc2 x ,(1- (ash 1 shift1))) ,m)
                        ,(- (+ shift1 shift2)))))))))))

;;; The following two asserts show the expected average case and worst case
;;; with respect to the complexity of the generated expression of the previous,
;;; function, under a word size of 32 bits:
#+sb-xc-host
(progn
  (assert (or (/= sb-vm:n-word-bits 32)
              (equal (gen-unsigned-div-by-constant-expr 10 most-positive-word)
                     '(ash (%multiply-high (logandc2 x 0) 3435973837) -3))))
  (assert (or (/= sb-vm:n-word-bits 32)
              (equal (gen-unsigned-div-by-constant-expr 7 most-positive-word)
                     '(let* ((num x)
                            (t1 (%multiply-high num 613566757)))
                       (ash
                        (truly-the word
                                   (+ t1 (ash (truly-the word (- num t1)) -1)))
                        -2))))))

;;; Return an expression for calculating the quotient like in the previous
;;; function, but the arguments have to fit in signed words.
;;; The algorithm is taken from the same paper, Figure 5.2

(defun gen-signed-div-by-constant-expr (y min-x max-x)
  (declare (type (or (integer #.(- (expt 2 (1- sb!vm:n-word-bits))) -3)
                     (integer 3 #.(expt 2 (1- sb!vm:n-word-bits)))) y)
           (type sb!vm:signed-word min-x max-x))
  (aver (not (zerop (logand (abs y) (1- (abs y))))))
  (aver (<= min-x max-x))
  (flet ((ld (x)
             ;; the floor of the binary logarithm of (positive) X
             (integer-length (1- x)))
           (add-extension (expr)
             (setq expr `(- ,expr
                            (ash num ,(- sb!vm:n-word-bits))))
             (when (minusp y)
               (setq expr `(- ,expr)))
             (let ((max (truncate max-x y))
                   (min (truncate min-x y)))
               (when (minusp y) (rotatef min max))
               (setq expr `(let ((num x))
                             (truly-the (integer ,min ,max)
                                        ,expr))))
             expr))
    (let* ((n (expt 2 (1- sb!vm:n-word-bits)))
           (precision (max (integer-length min-x) (integer-length max-x))))
      (multiple-value-bind (m shift)
          (choose-direct-multiplier (abs y) (max (abs max-x) (abs min-x)))
        (cond
          ((and (< (max (* max-x m) (* min-x m)) n)
                (>= (min (* max-x m) (* min-x m)) (- n)))
           (add-extension
            `(ash (* num ,m) ,(- shift))))
          (t
           (multiple-value-setq (m shift)
             (choose-multiplier (abs y) precision))
           (cond ((>= m n)
                  (add-extension
                   `(ash (truly-the
                          sb!vm:signed-word
                          (+ num
                             (%signed-multiply-high num ,(- m (* 2 n)))))
                         ,(- shift))))
                 ((zerop shift)
                  ;; Determine the range of the quotient before
                  ;; ADD-EXTENSION is applied to it
                  (let ((max (truncate max-x (abs y)))
                         (min (truncate min-x (abs y))))
                    (setq min (1- min))
                    (add-extension
                      ;; Explicit TRULY-THE needed to get the FIXNUM=>FIXNUM
                      ;; VOP.
                      `(truly-the (integer ,min ,max)
                                  (%signed-multiply-high num ,m)))))
                 (t
                  (add-extension
                   `(ash (%signed-multiply-high num ,m)
                         ,(- shift)))))))))))

;;; The following two asserts show the expected average case and worst case
;;; with respect to the complexity of the generated expression of the previous,
;;; function, under a word size of 32 bits:
#+sb-xc-host
(progn
  (assert (or (/= sb!vm:n-word-bits 32)
              (equal
               (gen-signed-div-by-constant-expr 11
                                     (- (expt 2 (1- sb!vm:n-word-bits)))
                                     (1- (expt 2 (1- sb!vm:n-word-bits))))
               '(let ((num x))
                 (truly-the (integer -195225786 195225786)
                            (- (ash (%signed-multiply-high num 780903145) -1)
                               (ash num -32)))))))
  (assert (or (/= sb!vm:n-word-bits 32)
              (equal
               (gen-signed-div-by-constant-expr 7
                                     (- (expt 2 (1- sb!vm:n-word-bits)))
                                     (1- (expt 2 (1- sb!vm:n-word-bits))))
               '(let ((num x))
                 (truly-the (integer -306783378 306783378)
                  (- (ash
                      (truly-the sb!vm:signed-word
                                 (+ num (%signed-multiply-high num -1840700269)))
                      -2)
                   (ash num -32))))))))

;;; If the divisor is constant and both args are positive and fit in a
;;; machine word, replace the division by a multiplication and possibly
;;; some shifts and an addition. Calculate the remainder by a second
;;; multiplication and a subtraction. Dead code elimination will
;;; suppress the latter part if only the quotient is needed. If the type
;;; of the dividend allows to derive that the quotient will always have
;;; the same value, emit much simpler code to handle that. (This case
;;; may be rare but it's easy to detect and the compiler doesn't find
;;; this optimization on its own.)
(deftransform truncate ((x y) (word (constant-arg word))
                        *
                        :policy (and (> speed compilation-speed)
                                     (> speed space)))
  "convert unsigned integer division to multiplication"
  (let* ((y      (lvar-value y))
         (x-type (lvar-type x))
         (max-x  (or (and (numeric-type-p x-type)
                          (numeric-type-high x-type))
                     most-positive-word)))
    ;; Division by zero, one or powers of two is handled elsewhere.
    (when (zerop (logand y (1- y)))
      (give-up-ir1-transform))
    `(let* ((quot ,(gen-unsigned-div-by-constant-expr y max-x))
            (rem (ldb (byte #.sb!vm:n-word-bits 0)
                      (- x (* quot ,y)))))
       (values quot rem))))

;;; Similar to previous transform, but with signed args
(deftransform truncate ((x y) (sb!vm:signed-word
                               (constant-arg sb!vm:signed-word))
                        *
                        :policy (and (> speed compilation-speed)
                                     (> speed space)))
  "convert signed integer division to multiplication"
  (let* ((y      (lvar-value y))
         (x-type (lvar-type x))
         (max-x  (or (and (numeric-type-p x-type)
                          (numeric-type-high x-type))
                     (- (expt 2 (1- sb!vm:n-word-bits)) 1)))
         (min-x  (or (and (numeric-type-p x-type)
                          (numeric-type-low x-type))
                     (- (expt 2 (1- sb!vm:n-word-bits))))))
    ;; Division by zero, one or powers of two is handled elsewhere.
    (when (zerop (logand (abs y) (1- (abs y))))
      (give-up-ir1-transform))
    `(let* ((quot ,(gen-signed-div-by-constant-expr y min-x max-x))
            (rem (truly-the (integer ,(- 1 (abs y)) ,(- (abs y) 1))
                            (- x (* quot ,y)))))
       (values quot rem))))
