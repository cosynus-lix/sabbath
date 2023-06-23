size_str = "10";
x_data = x.data;
u_data = u.data;
last_moment = length(x_data);

data = [x_data, u_data];
data(:, end-1) = -data(:, end-1);

lyap_0_fun = @(x) lyap0_fun(x', size_str);
val_lyap_0 = zeros(1, last_moment);
for l = 1 : last_moment
    val_lyap_0(l) = lyap_0_fun(data(l,:));
end
figure
semilogy(val_lyap_0)
hold on
issorted(-val_lyap_0)


lyap_1_fun = @(x) lyap1_fun(x', size_str);
val_lyap_1 = zeros(1, last_moment);
for l = 1 : last_moment
    val_lyap_1(l) = lyap_1_fun(data(l,:));
end
semilogy(val_lyap_1)
issorted(-val_lyap_1)


pc_lyap = @(x) piecewise_lyap(x', size_str);
val_lyap_pc = zeros(1, last_moment);
for l = 1 : last_moment
    val_lyap_pc(l) = pc_lyap(data(l,:));
end
semilogy(val_lyap_pc, 'o')
issorted(-val_lyap_pc)


diff_Val = zeros (1, length(val_lyap_0)-1);
for indexhere = 1:length(val_lyap_0)-1
diff_Val(indexhere) = val_lyap_0(indexhere) - val_lyap_0(indexhere + 1);
end
[ll, lll] = min(diff_Val)

diff_Val = zeros (1, length(val_lyap_1)-1);
for indexhere = 1:length(val_lyap_1)-1
diff_Val(indexhere) = val_lyap_1(indexhere) - val_lyap_1(indexhere + 1);
end
[ll, lll] = min(diff_Val)



diff_Val = zeros (1, length(val_lyap_pc)-1);
for indexhere = 1:length(val_lyap_pc)-1
diff_Val(indexhere) = val_lyap_pc(indexhere) - val_lyap_pc(indexhere + 1);
end
[ll, lll] = min(diff_Val)