function AF = restric_to_cod2_hyperplane(A, H1, H2)
%RESTRIC_TO_HYP Gives a description of a polynomial of degree 2 (not
%necessarily homogeneous) to an affine cod2 hyperplane.
% A is the matrix of the polynomial, described as p(x) = [x 1]' A [x 1].
% h is the vector of the hyperplane and c the constant, 
% the equations are [h1, -c1] * [x ; 1] = 0 AND [h2, -c2] * [x ; 1] . 
% H2 = [h2, -c2]. H1 = [h1, -c1].

L=length(H1);
h1 = H1(1:L-1);
c1 = -H1(L);
h2 = H2(1:L-1);
c2 = -H2(L);

N=size(A,1);
D=diag(A);
assert(norm(A-diag(D))/norm(A) < 1e-5)
assert(all(D(1:N-1)>0))

[~, max_ind1] = max(abs(h1));
max_val1 = h1(max_ind1);


[~, max_ind2] = max(abs(h2));
max_val2 = h2(max_ind2);

AF = A;
AF([max_ind1, max_ind2], :) = [];
AF(:, [max_ind1, max_ind2]) = [];

if max_ind1 > max_ind2
    coord_x_max1 = [-h1/max_val1 , c1/max_val1];
    new_H2 = H2 + H2(max_ind1) * coord_x_max1;
    new_H2(max_ind1)=[];
    coord_x_max1(max_ind1)=[];
    mat_to_add1 = coord_x_max1' * coord_x_max1;
    mat_to_add1 = A(max_ind1, max_ind1) * mat_to_add1;

    AF = A;
    AF(max_ind1, :) = [];
    AF(:, max_ind1) = [];

    AF = AF + mat_to_add1;
    [AF2, change_basis]= diagonalize_pol_deg_2(AF);
    new_H2 = new_H2 * change_basis;
    AF = restric_to_hyperplane(AF2, new_H2);
else
    coord_x_max2 = [-h2/max_val2 , c2/max_val2];
    new_H1 = H1 + H1(max_ind2) * coord_x_max2;
    new_H1(max_ind2)=[];
    coord_x_max2(max_ind2)=[];
    mat_to_add2 = coord_x_max2' * coord_x_max2;
    mat_to_add2 = A(max_ind2, max_ind2) * mat_to_add2;

    AF = A;
    AF(max_ind2, :) = [];
    AF(:, max_ind2) = [];

    AF = AF + mat_to_add2;
    [AF2, change_basis]= diagonalize_pol_deg_2(AF);
    new_H1 = new_H1 * change_basis;
    AF = restric_to_hyperplane(AF2, new_H1);
end


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

end

