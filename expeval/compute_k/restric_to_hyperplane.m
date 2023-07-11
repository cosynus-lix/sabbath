function A1 = restric_to_hyperplane(A, H)
%RESTRIC_TO_HYP Gives a description of a polynomial of degree 2 (not
%necessarily homogeneous) to an affine hyperplane.
% A is the matrix of the polynomial, described as p(x) = [x 1]' A [x 1].
% h is the vector of the hyperplane and c the constant, 
% the equation is [h, -c] * [x ; 1] = 0. H = [h, c].
L=length(H);
h = H(1:L-1);
c = -H(L);
N=size(A,1);
D=diag(A);
assert(norm(A-diag(D))/norm(A) < 1e-5)
assert(all(D(1:N-1)>0))
[~, max_ind] = max(abs(h));
max_val = h(max_ind);
A1 = A;
A1(max_ind, :) = [];
A1(:, max_ind) = [];
coord_x_max = [-h/max_val , c/max_val];
coord_x_max(max_ind)=[];
mat_to_add = coord_x_max' * coord_x_max;
% % This is a bad way to execute the previous line
% mat_to_add = zeros(N-1, N-1);
% for i1 = 1 : N -1
%     for i2 = 1 : N-1
%         if i1 == i2
%             mat_to_add(i1, i2) = coord_x_max(i1)^2;
%         else
%             mat_to_add(i1, i2) =  coord_x_max(i1)*coord_x_max(i2);
%         end
%     end
% end
mat_to_add = A(max_ind, max_ind) * mat_to_add;
A1 = A1 + mat_to_add;
end

