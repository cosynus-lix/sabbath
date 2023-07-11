function vol = compute_volume(A, k)
%COMPUTE_VOLUME computes the volume of the ellipse 
%  [x 1]' * A * [x 1] < k 
N = size(A, 1);
D=diag(A);
if (norm(A-diag(D))/norm(A) > 1e-5)
    A = diagonalize_pol_deg_2(A);
end
D=diag(A);
assert(norm(A-diag(D))/norm(A) < 1e-5)
assert(all(D(1:N-1)>0))
k1 = k - A(N,N);
if k1 <= 0
    vol = 0;
else
    A1 = A(1:N-1, 1:N-1);
    v1 = 1/sqrt(prod(diag((A1/k1))));
    vol = v1  * pi^((N-1)/2) / gamma((N-1)/2 +1);
end
end

